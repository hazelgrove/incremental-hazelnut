// open Hazelnut_lib.Incremental;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Update;
open Hazelnut_lib.Actions_random;

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
  // print_endline("all tests done.");
};

let string_of_list = (f, l) => {
  "[" ++ String.concat(", ", List.map(f, l)) ++ "]";
};

let string_of_action_list_list = l =>
  string_of_list(string_of_list(Hazelnut_lib.Pexp.string_of_action), l);
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

// let rec test_action = ic => {};

// let get_action_sequence = (ic, acc) => {
//   switch (test_action(ic)) {
//   | Comma(a) => get_action_sequence(ic)
//   | RBracket(a) => ()
//   };
// };

let child_of_string: string => Child.t =
  fun
  | "One" => One
  | "Two" => Two
  | "Three" => Three
  | _ => failwith("invalid child string");

let action_of_string: string => Iaction.t =
  fun
  | "MoveUp" => MoveUp
  | "Delete" => Delete
  | "InsertNumType" => InsertNumType
  | "WrapLam" => WrapLam
  | "WrapAsc" => WrapAsc
  | s =>
    if (String.length(s) > String.length("MoveDown")
        && String.sub(s, 0, String.length("MoveDown")) == "MoveDown") {
      let child_string =
        String.sub(
          s,
          String.length("MoveDown("),
          String.length(s) - String.length("MoveDown()"),
        );
      MoveDown(child_of_string(child_string));
    } else if (String.length(s) > String.length("WrapArrow")
               && String.sub(s, 0, String.length("WrapArrow")) == "WrapArrow") {
      let child_string =
        String.sub(
          s,
          String.length("WrapArrow("),
          String.length(s) - String.length("WrapArrow()"),
        );
      WrapArrow(child_of_string(child_string));
    } else if (String.length(s) > String.length("WrapPlus")
               && String.sub(s, 0, String.length("WrapPlus")) == "WrapPlus") {
      let child_string =
        String.sub(
          s,
          String.length("WrapPlus("),
          String.length(s) - String.length("WrapPlus()"),
        );
      WrapPlus(child_of_string(child_string));
    } else if (String.length(s) > String.length("WrapAp")
               && String.sub(s, 0, String.length("WrapAp")) == "WrapAp") {
      let child_string =
        String.sub(
          s,
          String.length("WrapAp("),
          String.length(s) - String.length("WrapAp()"),
        );
      WrapAp(child_of_string(child_string));
    } else if (String.length(s) > String.length("Unwrap")
               && String.sub(s, 0, String.length("Unwrap")) == "Unwrap") {
      let child_string =
        String.sub(
          s,
          String.length("Unwrap("),
          String.length(s) - String.length("Unwrap()"),
        );
      Unwrap(child_of_string(child_string));
    } else if (String.length(s) > String.length("InsertNumLit")
               && String.sub(s, 0, String.length("InsertNumLit"))
               == "InsertNumLit") {
      let num_string =
        String.sub(
          s,
          String.length("InsertNumLit("),
          String.length(s) - String.length("InsertNumLit()"),
        );
      InsertNumLit(int_of_string(num_string));
    } else if (String.length(s) > String.length("InsertVar")
               && String.sub(s, 0, String.length("InsertVar")) == "InsertVar") {
      // print_endline("insert var");
      // print_endline(string_of_int(String.length(s)));
      // print_endline(string_of_int(String.length("InsertVar((")));
      // print_endline(
      //   string_of_int(String.length(s) - String.length("InsertVar(())")),
      // );
      // print_endline(String.sub(s, 11, 12));
      // print_endline("why");
      let x =
        String.sub(
          s,
          String.length("InsertVar(("),
          String.length(s) - String.length("InsertVar(())"),
        );
      InsertVar(x);
    } else {
      failwith("unknown parse case");
    };

let rec get_action_string = (ic, acc): (string, bool) => {
  switch (input_char(ic)) {
  | ',' => (acc, true)
  | ']' => (acc, false)
  | c => get_action_string(ic, acc ++ String.make(1, c))
  };
};

let rec get_action_sequence = (ic, acc): list(Iaction.t) => {
  let (action_string, continue) = get_action_string(ic, "");
  let action = action_of_string(action_string);
  let action_sequence = acc @ [action];
  if (continue) {
    get_action_sequence(ic, action_sequence);
  } else {
    action_sequence;
  };
};

let get_action_list = (ic): (list(Iaction.t), bool) => {
  let _ = input_char(ic); // [
  let action_sequence = get_action_sequence(ic, []);
  let last_char = input_char(ic);
  switch (last_char) {
  | ',' => (action_sequence, true)
  | ']' => (action_sequence, false)
  | _ => failwith("invalid character")
  };
};

let rec test_action_list_sequence = (ic, acc) => {
  let (action_list, continue) = get_action_list(ic);
  let action_list_sequence = acc @ [action_list];
  switch (test_actionses(action_list_sequence, ())) {
  | () =>
    if (continue) {
      test_action_list_sequence(ic, action_list_sequence);
    } else {
      action_list_sequence;
    }
  | exception _ =>
    let s = string_of_action_list_list(action_list_sequence);
    _write_string_to_file("trimmed_actions.txt", s);
    action_list_sequence;
  };
};

let rec remove_one_action = (prefix, middle, postfix) =>
  try({
    let actionses = prefix @ postfix;
    test_actionses(actionses, ());
    // no longer failing, must try removing a different one
    switch (postfix) {
    // unable to remove anything
    | [] => None
    | [middle', ...postfix'] =>
      // try removing something further down
      remove_one_action(prefix @ [middle], middle', postfix')
    };
  }) {
  // still failing
  | _ => Some(prefix @ postfix)
  };

let rec remove_actions_until_cant = actionses =>
  switch (remove_one_action([], List.hd(actionses), List.tl(actionses))) {
  | Some(actionses') => remove_actions_until_cant(actionses')
  | None => actionses
  };

let test_action_log = () => {
  let current_path = Sys.getcwd();
  let current_path =
    String.sub(
      current_path,
      0,
      String.length(current_path) - String.length("/_build/default/test"),
    )
    ++ "/test";
  let ic = open_in(current_path ++ "/random_action_10000.txt");
  let _ = input_char(ic); // [
  let prefix = test_action_list_sequence(ic, []);
  print_endline("trying to minimize");
  let minimized_actionses = remove_actions_until_cant(prefix);
  let s = string_of_action_list_list(minimized_actionses);
  _write_string_to_file("minimized_actions.txt", s);
  ();
};

// test_action_log();

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
  ("minimized", `Quick, test_actionses(minimized_test)),
  ("all", `Quick, test_actionses_all),
  ("random 10", `Quick, test_actionses(random_action_segments(10))),
  ("random 100", `Quick, test_actionses(random_action_segments(100))),
  ("random 1K", `Quick, test_actionses(random_action_segments(1000))),
  ("random 10K", `Quick, test_actionses(random_action_segments(10000))),
  ("random 100K", `Quick, test_actionses(random_action_segments(100000))),
  ("random 1M", `Quick, test_actionses(random_action_segments(1000000))),
];
