open Sys;
open Yojson;
open Unix;
open Core;
open PPrint;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Incremental;
open Hazelnut_lib.State;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Update;
open Hazelnut_lib.Marking;
open Ocaml_intrinsics;

let () = assert(Array.length(Sys.argv) == 2);

let file_path = "log/" ++ Sys.argv[1];

let () = print_endline("writing to file " ++ file_path);

let shell = cmd => {
  let in_channel = Core_unix.open_process_in(cmd);
  In_channel.iter_lines(in_channel, ~f=str => print_endline(str));
  let res = Core_unix.close_process_in(in_channel);
  switch (res) {
  | Ok () => ()
  | _ => failwith("shell failed")
  };
};

let () = shell("mkdir -p log/");
let () = shell("touch " ++ file_path);

let c = Stdio.Out_channel.create(file_path);

type estate = {
  root: Iexp.parent,
  istate: Istate.t,
};

let init_estate = () => {root: initial_root(), istate: initial_state()};

let apply_eaction = (es: estate, action: Iaction.t) => {
  {root: es.root, istate: apply_action(es.istate, action)};
};

let timed = (f: unit => 'a) => {
  let before = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  let result = f();
  let after = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  (after - before, result);
};

let incr_tyck = (es: estate): (int, estate) => {
  timed(() => {root: es.root, istate: all_update_steps(es.istate)});
};

let baseline_tyck = (es: estate): (int, estate) => {
  let (t, _) =
    timed(() => {
      let _ = marked_correctly(child_of_parent(es.root));
      ();
    });
  (t, {root: es.root, istate: all_update_steps(es.istate)});
};

let wrap: list(Iaction.t) = [
  WrapLam,
  MoveDown(One),
  InsertVar("x"),
  MoveUp,
  MoveDown(Two),
  InsertNumType,
  MoveUp,
];

let actions: list(Iaction.t) =
  [Iaction.InsertVar("x")]
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap
  @ wrap;

let handle = (name, f) => {
  let acc = ref(init_estate());
  let timed =
    List.map(
      actions,
      act => {
        let (t, e) = f(apply_eaction(acc^, act));
        acc := e;
        t;
      },
    );
  let () =
    List.iteri(
      timed,
      (i, t) => {
        open Yojson.Basic;
        let json =
          `Assoc([
            ("name", `String(name)),
            ("iter", `Int(i)),
            ("time", `Int(t)),
          ]);
        Yojson.to_channel(c, json);
        Stdio.Out_channel.newline(c);
      },
    );
  ();
};

let () = handle("incr", incr_tyck);
let () = handle("baseline", baseline_tyck);

let () = Stdio.Out_channel.close(c);
