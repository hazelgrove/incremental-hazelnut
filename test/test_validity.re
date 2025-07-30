// open Hazelnut_lib.Incremental;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.UpdateProcess;
// open Hazelnut_lib.Counterexample;
// open Hazelnut_lib.Actions_random;

// open Hazelnut_lib.Pexp;

let rec apply_actions = (actions: list(Iaction.t), s): Istate.t => {
  switch (actions) {
  | [] => s
  | [action, ...actions] =>
    let s' = apply_action(s, action);
    all_update_steps(s');
    // print_endline(
    //   string_of_pexp(pexp_of_iexp(s'.ephemeral.root.root_child, s')),
    // );
    apply_actions(actions, s');
  };
};

let apply_actions_and_test = (actions, s) => {
  let s' = apply_actions(actions, s);
  all_update_steps(s');
  // print_endline(
  //   string_of_pexp(pexp_of_iexp(s'.ephemeral.root.root_child, s')),
  // );
  switch (marked_correctly(s'.ephemeral.root.root_child)) {
  | Some(e') =>
    print_endline("failed test");
    print_endline("ERROR: see:");
    print_endline(
      string_of_pexp(pexp_of_iexp(s'.ephemeral.root.root_child, s')),
    );
    print_endline("should see:");
    print_endline(string_of_pexp(pexp_of_iexp(e', s')));
    failwith("failed test");
  | None => ()
  };
  s';
};

let rec test_actionses_rec = (actionses: list(list(Iaction.t)), s) => {
  switch (actionses) {
  | [] => ()
  | [actions, ...actionses] =>
    let s' = apply_actions_and_test(actions, s);
    test_actionses_rec(actionses, s');
  };
};

let test_actionses = (actionses: list(list(Iaction.t)), ()) => {
  let s = initial_state();
  test_actionses_rec(actionses, s);
  // print_endline("all tests done.");
};

let string_of_list = (f, l) => {
  "[" ++ String.concat(",", List.map(f, l)) ++ "]";
};

let string_of_action_list_list = l =>
  string_of_list(string_of_list(Hazelnut_lib.Pexp.string_of_action), l);

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

let test_typfuns_1: list(list(Iaction.t)) = [
  [WrapAsc, MoveDown(Two), InsertTypVar("x"), MoveUp],
  [WrapTypFun],
  [
    MoveDown(One),
    InsertTypVar("x"),
    MoveUp,
    WrapTypAp,
    MoveDown(Two),
    InsertTypVar("x"),
  ],
];

let test_typfuns_2: list(list(Iaction.t)) = [
  [
    WrapTypFun,
    MoveDown(One),
    InsertTypVar("x"),
    MoveUp,
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
  ],
  [MoveDown(Three), MoveDown(Two), InsertVar("x"), WrapAsc],
  [MoveDown(Two), InsertTypVar("x")],
];

let test_typfuns_3: list(list(Iaction.t)) = [
  [
    WrapTypFun,
    MoveDown(One),
    InsertTypVar("x"),
    MoveUp,
    MoveDown(Two),
    WrapForAll,
    MoveDown(One),
    InsertTypVar("x"),
    MoveUp,
    MoveDown(Two),
    WrapArrow(One),
  ],
  [
    MoveDown(One),
    InsertTypVar("x"),
    MoveUp,
    MoveDown(Two),
    InsertNumType,
    MoveUp,
    MoveUp,
  ],
  [MoveDown(One), Delete],
  [
    InsertTypVar("x"),
    MoveUp,
    MoveUp,
    WrapTypAp,
    MoveDown(Two),
    InsertNumType,
    MoveUp,
    MoveDown(One),
    MoveDown(One),
    Delete,
  ],
];

let minimized_test: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    Delete,
    InsertVar("x"),
  ],
];

let minimized_2: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    Unwrap(One),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
  ],
];

let minimized_3: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapPlus(One),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    MoveDown(Two),
    WrapArrow(One),
  ],
  [MoveUp, Unwrap(One)],
];

let minimized_4: list(list(Iaction.t)) = [
  [
    InsertVar("x"),
    WrapPlus(One),
    MoveDown(Two),
    InsertVar("x"),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    Delete,
    InsertVar("x"),
  ],
];
let minimized_5: list(list(Iaction.t)) = [
  [
    WrapLam,
    WrapAsc,
    WrapPlus(One),
    WrapLam,
    WrapAsc,
    WrapPlus(One),
    WrapPlus(One),
    MoveDown(One),
    WrapLam,
    MoveUp,
    WrapPlus(One),
    WrapPlus(One),
    WrapAsc,
    WrapAp(One),
    MoveDown(One),
    WrapPlus(One),
    WrapPlus(Two),
    MoveUp,
    WrapAp(One),
    WrapPlus(One),
    Unwrap(One),
    WrapAp(One),
    Unwrap(Two),
    WrapAp(One),
    Unwrap(Two),
    WrapPlus(One),
    WrapLam,
    Unwrap(One),
    WrapAsc,
    WrapPlus(One),
    WrapAp(Two),
    WrapPlus(Two),
    WrapAp(Two),
    WrapAsc,
    Unwrap(Two),
    WrapAp(One),
    WrapLam,
    WrapAsc,
    WrapPlus(One),
    WrapAsc,
    WrapLam,
    WrapLam,
    WrapPlus(One),
    WrapLam,
    WrapAp(Two),
    WrapPlus(One),
    WrapAp(Two),
    WrapLam,
    WrapAsc,
    WrapAp(Two),
    WrapAsc,
    MoveDown(One),
    WrapAp(Two),
    MoveUp,
    Unwrap(Two),
    WrapLam,
    WrapPlus(Two),
    Unwrap(One),
    WrapAsc,
    WrapAsc,
    WrapLam,
    WrapAp(One),
    Unwrap(One),
    WrapAp(Two),
    Unwrap(One),
    WrapLam,
    WrapAp(Two),
    WrapPlus(Two),
    WrapPlus(Two),
    MoveDown(Two),
    WrapLam,
    MoveDown(One),
    InsertVar("x"),
    MoveUp,
    MoveUp,
    MoveDown(One),
    InsertVar("x"),
  ],
];

Random.self_init();

let actual_tests = [
  // ("indepedence", `Quick, multi_test_indepedence),
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
  ("typfuns1", `Quick, test_actionses(test_typfuns_1)),
  ("typfuns2", `Quick, test_actionses(test_typfuns_2)),
  ("typfuns3", `Quick, test_actionses(test_typfuns_3)),
  ("minimized", `Quick, test_actionses(minimized_test)),
  ("minimized 2", `Quick, test_actionses(minimized_2)),
  ("minimized 3", `Quick, test_actionses(minimized_3)),
  ("minimized 4", `Quick, test_actionses(minimized_4)),
  ("minimized 5", `Quick, test_actionses(minimized_5)),
  ("all", `Quick, test_actionses_all),
];

let validity_tests = actual_tests;
