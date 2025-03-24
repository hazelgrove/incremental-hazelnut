open Sys;
open Yojson;
open Unix;
open Core;
open PPrint;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Hazelnut;
open Hazelnut_lib.Incremental;
open Hazelnut_lib.State;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Actions_random;
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

let timed = (f: unit => 'a) => {
  let before = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  let result = f();
  let after = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  (after - before, result);
};

let incr_tyck = (es: Istate.t): (int, Istate.t) => {
  timed(() => {
    all_update_steps(es);
    es;
  });
};

let baseline_tyck = (es: Istate.t): (int, Istate.t) => {
  let bare_e = erase_upper(es.ephemeral.root.root_child);
  let (t, _) = timed(() => {performance_mark(bare_e)});
  all_update_steps(es);
  (t, es);
};

type exp =
  | [@deriving sexp] Hole
  | Lit(int)
  | Var(string)
  | Let(exp, exp, exp)
  | Lam(exp, exp, exp)
  | Zro(exp)
  | Fst(exp)
  | Tup(exp, exp)
  | Prod(exp, exp)
  | Arrow(exp, exp)
  | List
  | Unit
  | Int
  | Lt
  | Nil
  | Cons
  | /** List -> 'a -> (Num -> List -> 'a) -> 'a */
    ListMatch(exp)
  | /** 'a -> (Num -> 'a -> 'a) -> List -> 'a */
    ListRec(exp)
  | /** (('a -> 'a) -> ('a -> 'a)) -> ('a -> 'a) */
    Y(exp)
  | ITE(exp)
  | App(exp, exp);

// should only be one level deep - an node where all children is Hole
type hexp = exp;

type action =
  | Down(int)
  | Up
  | Replace(hexp)
  | ReplaceDown(int)
  | ReplaceUp(hexp, int);

let app2 = (f: exp, a: exp, b: exp) => App(App(f, a), b);

let app3 = (f: exp, a: exp, b: exp, c: exp) => App(app2(f, a, b), c);

let const = (x: exp) => Lam(Var("_"), Unit, x);

let lam2 = (x: exp, xt: exp, y: exp, yt: exp, b: exp) =>
  Lam(x, xt, Lam(y, yt, b));

let ite = (ty, i, t, e) => app3(ITE(ty), i, const(t), const(e));

let list_rec =
    (
      t: exp,
      base_case: exp,
      cons_x_name: exp,
      cons_xs_name: exp,
      cons_case: exp,
      list: exp,
    ) =>
  app3(
    ListRec(t),
    base_case,
    lam2(cons_x_name, Int, cons_xs_name, t, cons_case),
    list,
  );

let list_match =
    (
      t: exp,
      list: exp,
      base_case: exp,
      cons_x_name: exp,
      cons_xs_name: exp,
      cons_case: exp,
    ) =>
  app3(
    ListMatch(t),
    list,
    base_case,
    lam2(cons_x_name, Int, cons_xs_name, List, cons_case),
  );

let y = (t: exp, self: exp, impl: exp) => App(Y(t), Lam(self, t, impl));
let cons = (x: exp, xs: exp) => app2(Cons, x, xs);

let let_ = (lhs, ty, rhs, body) => App(Lam(lhs, ty, body), rhs)

let merge =
  y(
    Arrow(List, Arrow(List, List)),
    Var("merge"),
    lam2(
      Var("xs"),
      List,
      Var("ys"),
      List,
      list_match(
        List,
        Var("xs"),
        Var("ys"),
        Var("x"),
        Var("xs"),
        list_match(
          List,
          Var("ys"),
          cons(Var("x"), Var("xs")),
          Var("y"),
          Var("ys"),
          ite(
            List,
            app2(Lt, Var("x"), Var("y")),
            cons(
              Var("x"),
              app2(Var("merge"), Var("xs"), cons(Var("y"), Var("ys"))),
            ),
            cons(
              Var("y"),
              app2(Var("merge"), cons(Var("x"), Var("xs")), Var("ys")),
            ),
          ),
        ),
      ),
    ),
  );
/**fun (xs:[Int], ys:[Int]) ->
  case xs
    | [] => ys
    | x::xs =>
    case ys
      | [] => x::xs
      | y::ys => if x < y then x :: merge(xs, y::ys) else y :: merge(x::xs, ys)
    end
  end */
let split =
  Lam(
    Var("xs"),
    List,
    list_rec(
      Prod(List, List),
      Tup(Nil, Nil),
      Var("x"),
      Var("yszs"),
      Tup(cons(Var("x"), Fst(Var("yszs"))), Zro(Var("yszs"))),
      Var("xs"),
    ),
  );
/**split : [Int] -> ([Int], [Int]) =
  fun xs ->
    case xs
      | [] => ([], [])
      | x::xs =>
      let (ys, zs) = split(xs) in
      (x::zs, ys)
    end */
let mergesort = (merge, split) =>
  y(
    Arrow(List, List),
    Var("mergesort"),
    Lam(
      Var("xs"),
      List,
      list_match(
        List,
        Var("xs"),
        Nil,
        Var("x"),
        Var("xs"),
        list_match(
          List,
          Var("xs"),
          cons(Var("xs"), Nil),
          Var("_"),
          Var("_"),
          let_(
            Var("yszs"),
            Tup(List, List),
            App(split, Var("xs")),
            let_(
              Var("ys"),
              List,
              Zro(Var("yszs")),
              let_(
                Var("zs"),
                List,
                Fst(Var("yszs")),
                let_(
                  Var("ys"),
                  List,
                  App(Var("mergesort"), Var("ys")),
                  let_(
                    Var("zs"),
                    List,
                    App(Var("mergesort"), Var("zs")),
                    App(merge, Tup(Var("ys"), Var("zs"))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    ),
  );
/**mergesort : [Int] -> [Int] =
  fun xs ->
    case xs
      | [] => []
      | [x] => [x]
      | _ =>
      let (ys, zs) = split(xs) in
      let ys = mergesort(ys) in
      let zs = mergesort(zs) in
      merge(ys, zs)
    end */

let program =
  Let(
    Var("merge"),
    merge,
    Let(
      Var("split"),
      split,
      Let(
        Var("mergesort"),
        mergesort(Var("merge"), Var("split")),
        Var("mergesort"),
      ),
    ),
  );

let rec overlapping_mergesort = (n: int, bound) => {
  let_(
    Var("merge" ++ string_of_int(n)),
    Arrow(List, Arrow(List, List)),
    merge,
    let_(
      Var("split" ++ string_of_int(n)),
      Arrow(List, Tup(List, List)),
      split,
      let_(
        Var("mergesort"),
        Arrow(List, List),
        mergesort(
          Var("merge" ++ string_of_int(Random.int(n + 1))),
          Var("split" ++ string_of_int(Random.int(n + 1))),
        ),
        if (n >= bound) {
          Var("mergesort");
        } else {
          overlapping_mergesort(n + 1, bound);
        },
      ),
    ),
  );
};

let program = overlapping_mergesort(0, 10);

let rec case_name = (x: exp): string =>
  switch (x) {
  | Hole => "Hole"
  | Var(v) => "Var"
  | App(f, xs) => "App"
  | Let(lhs, rhs, body) => "Let"
  | ListMatch(_) => "ListMatch"
  | Tup(x, y) => "Tup"
  | Lit(i) => "Lit"
  | Lam(arg_name, arg_type, body) => "Lam"
  | List => "List"
  | Prod(x, y) => "Prod"
  | Int => "Int"
  | Zro(x) => "Zro"
  | Fst(x) => "Fst"
  | Nil => "Nil"
  | Cons => "Cons"
  | ITE(t) => "Ite"
  | Lt => "Lt"
  | Arrow(_, _) => "Arrow"
  | Unit => "Unit"
  | ListRec(_) => "ListRec"
  | Y(_) => "Y"
  };

let rec pprint = (x: exp): PPrint.document =>
  switch (x) {
  | Hole => string("HOLE")
  | Var(v) => string(v)
  | App(f, xs) => pprint(f) ^^ string("(") ^^ pprint(xs) ^^ string(")")
  | Let(lhs, rhs, body) =>
    string("let ")
    ^^ pprint(lhs)
    ^^ string(" = ")
    ^^ pprint(rhs)
    ^^ string(" in")
    ^^ group(break(1) ^^ pprint(body))
  | ListMatch(ty) =>
    string("ListMatch @") ^^ pprint(ty)
  | Tup(x, y) =>
    string("(") ^^ pprint(x) ^^ string(", ") ^^ pprint(y) ^^ string(")")
  | Arrow(x, y) =>
    string("(") ^^ pprint(x) ^^ string(" -> ") ^^ pprint(y) ^^ string(")")
  | Lit(i) => string(string_of_int(i))
  | Lam(arg_name, arg_type, body) =>
    string("fun ")
    ^^ pprint(arg_name)
    ^^ string(": ")
    ^^ pprint(arg_type)
    ^^ string(" -> ")
    ^^ pprint(body)
  | List => string("[") ^^ string("int") ^^ string("]")
  | Prod(x, y) => pprint(x) ^^ string(" * ") ^^ pprint(y)
  | Int => string("int")
  | Zro(x) => pprint(x) ^^ string(".0")
  | Fst(x) => pprint(x) ^^ string(".1")
  | Nil => string("[]@int")
  | Cons => string("Cons")
  | ITE(ty) => string("ITE @") ^^ pprint(ty)
  | ListRec(ty) => string("ListRec @") ^^ pprint(ty)
  | Lt => string("Lt")
  | Unit => string("Unit")
  | Y(ty) => string("Y @") ^^ pprint(ty)
  | _ =>
    print_endline(case_name(x));
    failwith("pprint");
  };

let rec pprint_action = (x: action): PPrint.document =>
  switch (x) {
  | Up => string("Up")
  | Down(i) => string("Down " ++ string_of_int(i))
  | Replace(x) => string("Replace ") ^^ pprint(x)
  | ReplaceDown(i) => string("ReplaceDown " ++ string_of_int(i))
  | ReplaceUp(x, i) =>
    string("ReplaceUp ") ^^ pprint(x) ^^ string(" " ++ string_of_int(i))
  };

let pretty_print = x => {
  PPrint.ToChannel.pretty(0.8, 160, Stdio.Out_channel.stdout, pprint(x));
  print_endline("");
};

let pretty_print_action = x => {
  PPrint.ToChannel.pretty(
    0.8,
    160,
    Stdio.Out_channel.stdout,
    pprint_action(x),
  );
  print_endline("");
};

type context = list(exp => exp);

let shuffle = d => {
  let nd = List.map(d, c => (Random.bits(), c));
  let sond = List.sort(nd, (x, y) => compare(fst(x), fst(y)));
  List.map(sond, snd);
};

let rec subedits = (x: exp, loc: int) => {
  [Down(loc)] @ edits(x) @ [Up];
}
and edits = (x: exp) => {
  switch (x) {
  | ListMatch(x) =>
    [Replace(ListMatch(Hole))]
    @ List.join(
        shuffle([
          subedits(x, 0),
        ]),
      )
  | Let(lhs, rhs, body) =>
    [Replace(Let(Hole, Hole, Hole))]
    @ List.join(
        shuffle([subedits(lhs, 0), subedits(rhs, 1), subedits(body, 2)]),
      )
  | Lam(arg_name, arg_type, body) =>
    [Replace(Lam(Hole, Hole, Hole))]
    @ List.join(
        shuffle([
          subedits(arg_name, 0),
          subedits(arg_type, 1),
          subedits(body, 2),
        ]),
      )
  | ITE(ty) =>
    [Replace(ITE(Hole))] @ List.join(shuffle([subedits(ty, 0)]))
  | ListRec(ty) =>
    [Replace(ListRec(Hole))] @ List.join(shuffle([subedits(ty, 0)]))
  | App(f, xs) =>
    [Replace(App(Hole, Hole))]
    @ List.join(shuffle([subedits(f, 0), subedits(xs, 1)]))
  | Arrow(x, y) =>
    [Replace(Arrow(Hole, Hole))]
    @ List.join(shuffle([subedits(x, 0), subedits(y, 1)]))
  | Tup(l, r) =>
    [Replace(Tup(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Prod(l, r) =>
    [Replace(Prod(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Zro(x) => [Replace(Zro(Hole))] @ subedits(x, 0)
  | Fst(x) => [Replace(Fst(Hole))] @ subedits(x, 0)
  | Y(x) => [Replace(Y(Hole))] @ subedits(x, 0)
  | Nil
  | Unit
  | Lt
  | Cons
  | List
  | Var(_)
  | Int => [Replace(x)]
  | _ =>
    pretty_print(x);
    failwith("edits");
  };
};

let wrap_insert = [
  ReplaceUp(Lam(Hole, Hole, Hole), 2),
  Down(0),
  Replace(Var("x")),
  Up,
  Down(1),
  Replace(Int),
  Up,
];
let wrap_delete = [ReplaceDown(0)];
let wrap_amount = 5000;
/*let trace =
  List.join(
    List.init(wrap_amount, (f) =>
      (
        {
          wrap_insert;
        }: _
      )
    ),
  );*/
// List.join(
//   List.init(wrap_amount, (f) =>
//     (
//       {
//         edits(program);
//       }: _
//     )
//   ),
// );
// );
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program);
// @ List.join(
//     List.init(wrap_amount, (f) =>
//       (
//         {
//           wrap_delete;
//         }: _
//       )
//     ),
//   );

let trace = edits(program)

let go_down = (x: exp, ctx: context, i: int): (exp, context) =>
  switch (x) {
  | Let(lhs, rhs, body) =>
    if (i == 0) {
      (lhs, [(x => Let(x, rhs, body)), ...ctx]);
    } else if (i == 1) {
      (rhs, [(x => Let(lhs, x, body)), ...ctx]);
    } else if (i == 2) {
      (body, [(x => Let(lhs, rhs, x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ITE(ty) =>
    if (i == 0) {
      (ty, [(x => ITE(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ListRec(ty) =>
    if (i == 0) {
      (ty, [(x => ListRec(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Lam(arg_name, arg_type, body) =>
    if (i == 0) {
      (arg_name, [(x => Lam(x, arg_type, body)), ...ctx]);
    } else if (i == 1) {
      (arg_type, [(x => Lam(arg_name, x, body)), ...ctx]);
    } else if (i == 2) {
      (body, [(x => Lam(arg_name, arg_type, x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ListMatch(ty) =>
    if (i == 0) {
      (ty, [(x => ListMatch(ty)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Zro(x) =>
    if (i == 0) {
      (x, [(x => Zro(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Fst(x) =>
    if (i == 0) {
      (x, [(x => Zro(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Prod(x, y) =>
    if (i == 0) {
      (x, [(x => Prod(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Prod(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Arrow(x, y) =>
    if (i == 0) {
      (x, [(x => Arrow(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Arrow(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | App(x, y) =>
    if (i == 0) {
      (x, [(x => App(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => App(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Tup(x, y) =>
    if (i == 0) {
      (x, [(x => Tup(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Tup(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | _ =>
    pretty_print(x);
    failwith("godown");
  };

let go_up = (x: exp, ctx: context): (exp, context) =>
  switch (ctx) {
  | [c, ...ctx] => (c(x), ctx)
  };

let rec uppest = (x: exp, ctx: context) =>
  switch (ctx) {
  | [] => x
  | [c, ...ctx] => uppest(c(x), ctx)
  };
let step_trace = (x: exp, ctx: context, act: action): (exp, context) => {
  switch (act) {
  | Down(i) => go_down(x, ctx, i)
  | Up => go_up(x, ctx)
  | Replace(x) => (x, ctx)
  };
};

let rec apply_traces = (x: exp, ctx: context, act) => {
  if (false && List.length(ctx) % 10 == 0) {
    pretty_print(uppest(x, ctx));
  };
  switch (act) {
  | [] => x
  | [act, ...acts] =>
    let (x, ctx) = step_trace(x, ctx, act);
    apply_traces(x, ctx, acts);
  };
};

// apply_traces(Hole, [], trace);

let wrap: list(Iaction.t) = [
  WrapPlus(Two),
  WrapLam,
  MoveDown(One),
  InsertVar("x"),
  MoveUp,
  MoveDown(Two),
  WrapArrow(One),
  MoveDown(One),
  InsertNumType,
  MoveUp,
  MoveUp,
];

let wraps =
  wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap;

let wraps = wraps @ wraps @ wraps @ wraps @ wraps @ wraps @ wraps @ wraps;
// let wraps = wraps @ wraps @ wraps @ wraps;

// let actions: list(Iaction.t) = [Iaction.InsertVar("x")] @ wraps;

// let actions = List.concat(random_action_segments(10000));

let to_iaction = (act: action) => {
  switch (act) {
  | Up => Iaction.MoveUp
  | ReplaceUp(Lam(Hole, Hole, Hole), 2) => Iaction.WrapLam
  | Replace(Arrow(Hole, Hole)) => Iaction.WrapArrow(One)
  | Replace(Prod(Hole, Hole)) => Iaction.WrapProduct(One)
  | Replace(Tup(Hole, Hole)) => Iaction.WrapPair(One)
  | Replace(Lam(Hole, Hole, Hole)) => Iaction.WrapLam
  | Replace(App(Hole, Hole)) => Iaction.WrapAp(One)
  | Replace(Zro(Hole)) => Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Fst)
  | Replace(Fst(Hole)) => Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Snd)
  | Replace(ListRec(Hole)) => Iaction.InsertListRec
  | Replace(Y(Hole)) => Iaction.InsertY
  | Replace(ITE(Hole)) => Iaction.InsertITE
  | Replace(ListMatch(Hole)) => Iaction.InsertListMatch
  | Replace(Nil) => Iaction.InsertNil
  | Replace(Lt) => Iaction.InsertLt
  | Replace(Cons) => Iaction.InsertCons
  | Replace(Var(x)) => Iaction.InsertVar(x)
  | Replace(Int) => Iaction.InsertNumType
  | Replace(List) => Iaction.InsertList
  | Replace(Unit) => Iaction.InsertUnitType
  | Down(0) => Iaction.MoveDown(One)
  | Down(1) => Iaction.MoveDown(Two)
  | Down(2) => Iaction.MoveDown(Three)
  | ReplaceDown(0) => Iaction.Unwrap(One)
  | ReplaceDown(1) => Iaction.Unwrap(Two)
  | ReplaceDown(2) => Iaction.Unwrap(Three)
  | _ =>
    pretty_print_action(act);
    failwith("to_iaction");
  };
};
let actions: list(Iaction.t) = List.map(trace, to_iaction); // @ List.concat(random_action_segments(10000));

let handle = (name, f) => {
  let acc = ref(initial_state());
  let timed =
    List.map(
      actions,
      act => {
        let (t, e) = f(apply_action(acc^, act));
        acc := e;
        (act, t);
      },
    );
  let () =
    List.iteri(
      timed,
      (i, (act, t)) => {
        open Yojson.Basic;
        let json =
          `Assoc([
            ("name", `String(name)),
            ("action", `String(string_of_action(act))),
            ("iter", `Int(i)),
            ("time", `Int(t)),
          ]);
        Yojson.to_channel(c, json);
        Stdio.Out_channel.newline(c);
      },
    );
  ();
};

let () = handle("baseline", baseline_tyck);
let () = handle("incr", incr_tyck);

let () = Stdio.Out_channel.close(c);
