open Hazelnut_lib.Incremental;
open Hazelnut_lib.Marking;

let apply_actions = (actions: list(Iaction.t), s): Istate.t => {
  List.fold_left(apply_action, s, actions);
};

let rec test_actionses_rec = (actionses: list(list(Iaction.t)), root, s) => {
  switch (actionses) {
  | [] => ()
  | [actions, ...actionses] =>
    let s' = all_update_steps(apply_actions(actions, s));
    switch (marked_correctly(child_of_parent(root))) {
    | Some(_) => failwith("failed test")
    | None => ()
    };
    test_actionses_rec(actionses, root, s');
  };
};

let test_actionses = (actionses: list(list(Iaction.t))) => {
  let root = initial_root;
  let s = initial_state;
  test_actionses_rec(actionses, root, s);
  print_endline("all tests done.");
};

let a1: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapPlus(One), WrapLam, MoveDown(One), InsertVar("x")],
  [MoveUp, MoveDown(Two), WrapArrow(One)],
];

let a2: list(list(Iaction.t)) = [
  [InsertVar("x"), WrapAp(One), WrapLam, MoveDown(One), InsertVar("x")],
  [MoveUp, MoveDown(Two), InsertNumType],
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

test_actionses(
  a1
  @ [[Iaction.Delete]]
  @ a2
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
  @ free_var,
);
