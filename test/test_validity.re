// open Hazelnut_lib.Incremental;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Update;

// open Hazelnut_lib.Pexp;

let apply_actions = (actions: list(Iaction.t), s): Istate.t => {
  List.fold_left(apply_action, s, actions);
};

let rec test_actionses_rec = (actionses: list(list(Iaction.t)), s) => {
  switch (actionses) {
  | [] => ()
  | [actions, ...actionses] =>
    let s' = apply_actions(actions, s);
    all_update_steps(s');
    switch (marked_correctly(s'.ephemeral.root.root_child)) {
    | Some(_) => failwith("failed test")
    | None => ()
    };
    test_actionses_rec(actionses, s');
  };
};

let test_actionses = (actionses: list(list(Iaction.t)), ()) => {
  let s = initial_state();
  test_actionses_rec(actionses, s);
  print_endline("all tests done.");
};

let random_motion = (): Iaction.t => {
  let r = Random.int(6);
  switch (r) {
  | 0
  | 1
  | 2 => MoveUp
  | 3 => MoveDown(One)
  | 4 => MoveDown(Two)
  | 5 => MoveDown(Three)
  | _ => failwith("bad random number")
  };
};

let random_motions = () => {
  List.init(Random.int(13), _ => random_motion());
};

let random_edit = (): list(Iaction.t) => {
  let r = Random.int(11);
  switch (r) {
  | 0 => [Delete]
  | 1 // => [WrapArrow(One)]
  | 2 // => [InsertNumType]
  | 3 // => [InsertNumLit(0)]
  | 4 => [InsertVar("x")]
  | 5 => [InsertVar("y")]
  | 6 // => [WrapPlus(One)]
  | 7 //=> [WrapAp(One)]
  | 8 //=> [WrapAsc]
  | 9 => [WrapLam, MoveUp, MoveDown(One), InsertVar("x"), MoveUp]
  | 10 => [WrapLam, MoveUp, MoveDown(One), InsertVar("y"), MoveUp]
  | _ => failwith("bad random number")
  };
};

let random_action_segment = () => random_motions() @ random_edit();

let string_of_list = (f, l) => {
  "[" ++ String.concat(", ", List.map(f, l)) ++ "]";
};

let _write_string_to_file = (filename, s) => {
  let current_path = Sys.getcwd();
  let current_path =
    String.sub(
      current_path,
      0,
      String.length(current_path) - String.length("/_build/default/test"),
    )
    ++ "/test";
  // print_endline(current_path);
  let oc = open_out(current_path ++ "/" ++ filename);
  output_string(oc, s);
  close_out(oc);
};

let random_action_segments = n => {
  let l = List.init(n, _ => random_action_segment());
  // let s =
  //   string_of_list(string_of_list(Hazelnut_lib.Pexp.string_of_action), l);
  // write_string_to_file("random_action_" ++ string_of_int(n) ++ ".txt", s);
  l;
};

let a1: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapPlus(One), WrapLam, MoveDown(One), InsertVar("x")],
  [MoveUp, MoveDown(Two), WrapArrow(One)],
];

let a1': list(list(Iaction.t)) = [[InsertVar("x")], [Delete]];

let a2: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapAp(One), WrapLam, MoveDown(One), InsertVar("x")],
  [MoveUp, MoveDown(Two), InsertNumType],
];

let a3: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    MoveDown(Two),
    InsertNumType,
  ],
];

let binding_insert: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapLam,
    MoveDown(Two),
    InsertNumType,
    MoveUp,
    MoveDown(One),
    InsertVar("x"),
  ],
];

let binding_delete: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    MoveDown(Two),
    InsertNumType,
    MoveUp,
    MoveDown(One),
    Delete,
  ],
];

let inconsistent: list(list(Iaction.t)) = [
  [WrapAsc, MoveDown(Two), WrapArrow(Two), MoveUp, WrapPlus(One)],
];

let non_arrow_ap: list(list(Iaction.t)) = [
  [InsertNumLit(4), WrapAp(One)],
];

let non_arrow_lam: list(list(Iaction.t)) = [
  [WrapLam, WrapAsc, MoveDown(Two), InsertNumType],
];

let lam_ann_inconsistent: list(list(Iaction.t)) = [
  [
    WrapLam,
    MoveDown(Two),
    WrapArrow(Two),
    MoveUp,
    WrapAsc,
    MoveDown(Two),
    WrapArrow(One),
    MoveDown(One),
    InsertNumType,
  ],
];

let free_var: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapLam, MoveDown(One), InsertVar("x"), Delete],
];

let big_example: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapAp(Two),
    MoveDown(One),
    WrapLam,
    MoveDown(One),
    InsertVar("y"),
    MoveUp,
    MoveDown(Two),
    InsertNumType,
    MoveUp,
    MoveDown(Three),
    WrapPlus(One),
    MoveDown(One),
    InsertVar("y"),
    MoveUp,
    MoveDown(Two),
    InsertVar("y"),
    WrapPlus(One),
    MoveDown(Two),
    InsertVar("x"),
    MoveUp,
    MoveUp,
    MoveUp,
    MoveUp,
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    MoveDown(Two),
    WrapArrow(One),
  ],
];

let big_example_broken_up: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapAp(Two), MoveDown(One), WrapLam],
  [MoveDown(One), InsertVar("y"), MoveUp],
  [MoveDown(Two), InsertNumType, MoveUp, MoveDown(Three), WrapPlus(One)],
  [MoveDown(One), InsertVar("y"), MoveUp, MoveDown(Two)],
  [InsertVar("y"), WrapPlus(One), MoveDown(Two), InsertVar("x")],
  [MoveUp, MoveUp, MoveUp, MoveUp],
  [WrapLam, MoveDown(One), InsertVar("x")],
  [MoveUp, MoveDown(Two), WrapArrow(One)],
];

let unwrap: list(list(Iaction.t)) = [
  [WrapPlus(One), Unwrap(One)],
  [WrapPlus(One)],
];

let nonsense: list(list(Iaction.t)) = [
  [WrapAp(Two), Unwrap(One), WrapAp(Two), WrapPlus(One)],
  [MoveDown(Two), InsertVar(""), InsertNumType, WrapArrow(Two), WrapLam],
  [Unwrap(Two), Unwrap(Two), Unwrap(Two)],
  [
    WrapPlus(Two),
    WrapAp(Two),
    WrapArrow(Two),
    InsertVar(""),
    MoveDown(Two),
    WrapArrow(Two),
    MoveUp,
    Delete,
    WrapPlus(Two),
    WrapAsc,
    InsertVar(""),
    MoveDown(Three),
    MoveDown(One),
    MoveDown(One),
    MoveDown(Two),
    WrapArrow(Two),
    InsertVar(""),
    WrapAp(One),
    WrapPlus(Two),
    Unwrap(Two),
    Delete,
    Unwrap(Two),
  ],
  [WrapPlus(Two), WrapAp(Two), WrapArrow(Two)],
  [MoveDown(Three), MoveDown(Two), MoveDown(Two)],
  [
    WrapLam,
    MoveDown(Three),
    WrapAp(Two),
    Delete,
    Delete,
    WrapLam,
    Unwrap(One),
    WrapLam,
    WrapPlus(One),
    WrapAp(One),
    WrapAp(Two),
    WrapAsc,
    InsertVar(""),
    WrapArrow(Two),
    WrapArrow(One),
    Unwrap(Two),
    MoveDown(Three),
    Delete,
    MoveDown(Two),
    Unwrap(Two),
    WrapAp(One),
    WrapAsc,
    WrapPlus(One),
    Unwrap(One),
    Unwrap(Two),
    WrapAp(Two),
    InsertNumType,
    WrapArrow(One),
    MoveDown(One),
    MoveDown(One),
    WrapArrow(One),
    WrapArrow(Two),
  ],
  [WrapLam, WrapAsc, WrapPlus(Two), Unwrap(Two)],
  [
    Delete,
    Unwrap(One),
    WrapPlus(Two),
    WrapAp(Two),
    WrapLam,
    WrapArrow(Two),
    MoveDown(Two),
    MoveDown(One),
    MoveUp,
    MoveDown(One),
    MoveDown(Two),
    WrapArrow(One),
    WrapArrow(One),
    InsertVar(""),
    WrapAp(One),
    WrapAsc,
    WrapPlus(Two),
    Unwrap(One),
  ],
  [Delete, WrapPlus(Two)],
  [WrapAsc, WrapAp(One), InsertVar("")],
  [WrapArrow(Two), MoveDown(Two), MoveDown(One)],
];

let excise: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    Iaction.Delete,
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
  ],
];

let excise2: list(list(Iaction.t)) = [
  [InsertVar("y"), WrapPlus(One), WrapLam, MoveDown(One), InsertVar("x")],
];

let test_actionses_all =
  test_actionses(
    a1
    @ [[Iaction.Delete]]
    @ a1'
    @ [[Iaction.Delete]]
    @ a2
    @ [[Iaction.Delete]]
    @ a3
    @ [[Iaction.Delete]]
    @ binding_insert
    @ [[Iaction.Delete]]
    @ binding_delete
    @ [[Iaction.Delete]]
    @ inconsistent
    @ [[Iaction.Delete]]
    @ non_arrow_ap
    @ [[Iaction.Delete]]
    @ non_arrow_lam
    @ [[Iaction.Delete]]
    @ lam_ann_inconsistent
    @ [[Iaction.Delete]]
    @ free_var
    @ [[Iaction.Delete]]
    @ big_example
    @ [[Iaction.Delete]]
    @ big_example_broken_up
    @ [[Iaction.Delete]]
    @ unwrap
    @ [[Iaction.Delete]]
    @ nonsense,
  );

type test_action_end =
  | Comma
  | RBracket;

let rec test_action = ic => {};

let rec test_action_sequence = ic => {
  switch (test_action(ic)) {
  | Comma => test_action_sequence(ic)
  | RBracket => ()
  };
};

let test_action_list = ic => {
  let _ = input_char(ic); // [
  test_action_sequence(ic);
};

let rec test_action_list_sequence = ic => {
  test_action_list(ic);
  let next_char = input_char(ic);
  switch (next_char) {
  | ',' => test_action_list_sequence(ic)
  | ']' => ()
  | _ => failwith("bad character")
  };
};

let test_action_log = () => {
  let ic = open_in("test/random_action_10000.txt");
  let _ = input_char(ic); // [
  test_action_list(ic);
};

let validity_tests = [
  ("a1", `Quick, test_actionses(a1)),
  ("a1'", `Quick, test_actionses(a1')),
  ("a2", `Quick, test_actionses(a2)),
  ("a3", `Quick, test_actionses(a3)),
  ("binding_insert", `Quick, test_actionses(binding_insert)),
  ("binding_delete", `Quick, test_actionses(binding_delete)),
  ("inconsistent", `Quick, test_actionses(inconsistent)),
  ("non_arrow_ap", `Quick, test_actionses(non_arrow_ap)),
  ("non_arrow_lam", `Quick, test_actionses(non_arrow_lam)),
  ("lam_ann_inconsistent", `Quick, test_actionses(lam_ann_inconsistent)),
  ("free_var", `Quick, test_actionses(free_var)),
  ("big_example", `Quick, test_actionses(big_example)),
  ("big_example_broken_up", `Quick, test_actionses(big_example_broken_up)),
  ("unwrap", `Quick, test_actionses(unwrap)),
  ("nonsense", `Quick, test_actionses(nonsense)),
  ("excise", `Quick, test_actionses(excise)),
  ("excise2", `Quick, test_actionses(excise2)),
  ("all", `Quick, test_actionses_all),
  ("random 10", `Quick, test_actionses(random_action_segments(10))),
  ("random 100", `Quick, test_actionses(random_action_segments(100))),
  ("random 1K", `Quick, test_actionses(random_action_segments(1000))),
  // ("random 2K", `Quick, test_actionses(random_action_segments(2000))),
  ("random 10K", `Quick, test_actionses(random_action_segments(10000))),
  // ("random 3K", `Quick, test_actionses(random_action_segments(3000))),
  // ("random 10K", `Quick, test_actionses(random_action_segments(10000))),
  // ("random-4", `Quick, test_actionses(random_action_segments(1024))),
  // ("random-3", `Quick, test_actionses(random_action_segments(1025))),
  // ("random-2", `Quick, test_actionses(random_action_segments(1026))),
  // ("random-1", `Quick, test_actionses(random_action_segments(1027))),
  // ("random0", `Quick, test_actionses(random_action_segments(1028))),
  // ("random1", `Quick, test_actionses(random_action_segments(1029))),
  // ("random2", `Quick, test_actionses(random_action_segments(1030))),
  // ("random3", `Quick, test_actionses(random_action_segments(1031))),
  // ("random4", `Quick, test_actionses(random_action_segments(1032))),
  // ("random5", `Quick, test_actionses(random_action_segments(1033))),
  // ("random6", `Quick, test_actionses(random_action_segments(1034))),
  // ("random7", `Quick, test_actionses(random_action_segments(1035))),
  // ("random8", `Quick, test_actionses(random_action_segments(1036))),
  // ("random9", `Quick, test_actionses(random_action_segments(1037))),
  // ("random10", `Quick, test_actionses(random_action_segments(1038))),
  // ("random11", `Quick, test_actionses(random_action_segments(1039))),
];
