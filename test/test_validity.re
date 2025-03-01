// open Hazelnut_lib.Incremental;
open Hazelnut_lib.Actions;
// open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Update;

let apply_actions = (actions: list(Iaction.t), s): Istate.t => {
  List.fold_left(apply_action, s, actions);
};

let rec test_actionses_rec = (actionses: list(list(Iaction.t)), root, s) => {
  switch (actionses) {
  | [] => ()
  | [actions, ...actionses] =>
    all_update_steps(apply_actions(actions, s));
    // switch (marked_correctly(child_of_parent(root))) {
    // | Some(_) => failwith("failed test")
    // | None => ()
    // };
    test_actionses_rec(actionses, root, s);
  };
};

let test_actionses = (actionses: list(list(Iaction.t))) => {
  let (root, s) = initial_root_and_state();
  test_actionses_rec(actionses, root, s);
  print_endline("all tests done.");
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

test_actionses(a1');

// a1 @ [[Iaction.Delete]]
//@ a2 //@ [[Iaction.Delete]] @ a3,
// @ [[Iaction.Delete]]
// @ binding_insert
// @ [[Iaction.Delete]]
// @ binding_delete
// @ [[Iaction.Delete]]
// @ inconsistent
// @ [[Iaction.Delete]]
// @ non_arrow_ap
// @ [[Iaction.Delete]]
// @ non_arrow_lam
// @ [[Iaction.Delete]]
// @ lam_ann_inconsistent
// @ [[Iaction.Delete]]
// @ free_var
// @ [[Iaction.Delete]]
// @ big_example
// @ [[Iaction.Delete]]
// @ big_example_broken_up
// @ [[Iaction.Delete]]
// @ unwrap
// @ [[Iaction.Delete]]
// @ nonsense;
