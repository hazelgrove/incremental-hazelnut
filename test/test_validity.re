// open Hazelnut_lib.Incremental;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Update;
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

let current_path = {
  let current_path = Sys.getcwd();
  if (String.sub(
        current_path,
        String.length(current_path) - String.length("/_build/default/test"),
        String.length("/_build"),
      )
      == "/_build") {
    String.sub(
      current_path,
      0,
      String.length(current_path) - String.length("/_build/default/test"),
    )
    ++ "/test";
  } else {
    current_path ++ "/test";
  };
};

let _write_string_to_file = (filename, s) => {
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

let minimized_6: list(list(Iaction.t)) = [
  [
    WrapAp(Two),
    WrapAp(Two),
    WrapAp(Two),
    WrapPlus(Two),
    WrapPlus(Two),
    WrapAp(Two),
    WrapAp(Two),
    WrapPlus(Two),
    WrapAp(One),
    WrapPlus(One),
    WrapAp(Two),
    WrapAp(One),
    WrapAsc,
    WrapAsc,
    WrapPlus(One),
    WrapAsc,
    WrapPlus(One),
    WrapPlus(One),
    WrapLam,
    WrapPlus(Two),
    WrapAp(One),
    WrapAp(One),
    WrapPlus(One),
    WrapAp(Two),
    WrapAp(Two),
    WrapAp(Two),
    WrapLam,
    WrapPlus(One),
    WrapLam,
    WrapLam,
    WrapPlus(Two),
    WrapAp(One),
    WrapAp(One),
    WrapLam,
    WrapAsc,
    WrapAp(Two),
    WrapLam,
    WrapLam,
    WrapAp(One),
    WrapPlus(One),
    WrapAp(One),
    WrapPlus(One),
    WrapPlus(One),
    WrapAp(One),
    WrapAp(One),
    WrapPlus(One),
    WrapPlus(One),
    WrapAp(Two),
    WrapAp(One),
    Unwrap(Two),
    WrapAp(Two),
    WrapPlus(One),
    Unwrap(One),
    MoveDown(Two),
    WrapLam,
    MoveUp,
    WrapAp(One),
    MoveDown(One),
    MoveDown(Two),
    WrapLam,
    MoveDown(Three),
    WrapAsc,
    MoveUp,
    MoveUp,
    MoveUp,
    MoveDown(Two),
    WrapAp(One),
    WrapLam,
    MoveUp,
    MoveDown(One),
    MoveDown(Two),
    MoveUp,
    Unwrap(Two),
  ],
];

// blatantly exponential, it'll never run
let rec find_best_failing_subset = (rev_acc: list(Iaction.t)) =>
  fun
  | [] => {
      let acc = List.rev(rev_acc);
      switch (test_actionses([acc], ())) {
      | exception _ => Some(acc)
      | _ => None
      };
    }
  | [h, ...t] => {
      switch (
        find_best_failing_subset(rev_acc, t),
        find_best_failing_subset([h, ...rev_acc], t),
      ) {
      | (None, r) => r
      | (r, None) => r
      | (Some(r1), Some(r2)) =>
        if (List.length(r1) > List.length(r2)) {
          Some(r2);
        } else {
          Some(r1);
        }
      };
    };

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

let rec remove_one_action = (rev_prefix, middle, postfix) => {
  let actionses = List.rev(rev_prefix) @ postfix;
  try(
    {
      test_actionses(actionses, ());
      // no longer failing, must try removing a different one
      switch (postfix) {
      // unable to remove anything
      | [] => None
      | [middle', ...postfix'] =>
        // try removing something further down
        remove_one_action([middle, ...rev_prefix], middle', postfix')
      };
    }
  ) {
  // still failing
  | _ => Some(actionses)
  };
};

let rec remove_actions_until_cant = actionses =>
  switch (remove_one_action([], List.hd(actionses), List.tl(actionses))) {
  | Some(actionses') => remove_actions_until_cant(actionses')
  | None => actionses
  };

let rec remove_one_little_action = (rev_prefix, middle, postfix) => {
  let actions = List.rev(rev_prefix) @ postfix;
  try(
    {
      test_actionses([actions], ());
      // no longer failing, must try removing a different one
      switch (postfix) {
      // unable to remove anything
      | [] => None
      | [middle', ...postfix'] =>
        // try removing something further down
        remove_one_little_action([middle, ...rev_prefix], middle', postfix')
      };
    }
  ) {
  // still failing
  | _ => Some(actions)
  };
};

let rec remove_little_actions_until_cant = actions =>
  switch (remove_one_little_action([], List.hd(actions), List.tl(actions))) {
  | Some(actions') => remove_little_actions_until_cant(actions')
  | None => actions
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
  let ic = open_in(current_path ++ "/old_prefix.txt");
  // let _ = failwith("opened");

  print_endline("parsing...");
  let _ = input_char(ic); // [
  let prefix = test_action_list_sequence(ic, []);
  // let _ = failwith("parsed");
  // print_endline("prefix length" ++ string_of_int(List.length(prefix)));
  // test_actionses(prefix, ());

  print_endline("minimizing...");
  let minimized_actionses = remove_actions_until_cant(prefix);
  let s = string_of_action_list_list(minimized_actionses);
  _write_string_to_file("minimized_actions.txt", s);
  ();
};

let rec probabilistic_minimizer_pass = (actionses, prob) =>
  if (prob < 0.00000001) {
    actionses;
  } else {
    let filtered_actionses =
      List.filter(_ => Random.float(1.0) < prob, actionses);
    switch (test_actionses(filtered_actionses, ())) {
    | () => probabilistic_minimizer_pass(actionses, prob *. 0.9) // took away too much
    | exception _ => probabilistic_minimizer_pass(filtered_actionses, 0.5) // successful filter, reset
    };
  };

let rec probabilistic_minimizer = (n, actionses) =>
  if (n == 0) {
    actionses;
  } else {
    let actionses' = probabilistic_minimizer_pass(actionses, 0.5);
    probabilistic_minimizer(n - 1, actionses');
  };

let rec little_probabilistic_minimizer_pass = (actions, prob) =>
  if (prob < 0.00000001) {
    actions;
  } else {
    let filtered_actions =
      List.filter(_ => Random.float(1.0) < prob, actions);
    switch (test_actionses([filtered_actions], ())) {
    | () => little_probabilistic_minimizer_pass(actions, prob *. 0.9) // took away too much
    | exception _ =>
      little_probabilistic_minimizer_pass(filtered_actions, 0.5) // successful filter, reset
    };
  };

let rec little_probabilistic_minimizer = (n, actions) =>
  if (n == 0) {
    actions;
  } else {
    let actions' = little_probabilistic_minimizer_pass(actions, 0.5);
    little_probabilistic_minimizer(n - 1, actions');
  };

let totally_minimize = prefix => {
  let prob_minimized = probabilistic_minimizer(10, prefix);
  let s = string_of_action_list_list(prob_minimized);
  _write_string_to_file("prob_minimized.txt", s);
  let minimized = remove_actions_until_cant(prob_minimized);
  let s = string_of_action_list_list(minimized);
  _write_string_to_file("minimized.txt", s);
  minimized;
};

// test_action_log();

let rec generate_minimal_counterexample = (fuel, s_acc, rev_acc) => {
  let deal_with_countexample = prefix => {
    print_endline(
      "counterexample found with prefix length "
      ++ string_of_int(List.length(prefix)),
    );
    print_endline("this better fail...");
    switch (test_actionses(prefix, ())) {
    | exception _ => ()
    | _ => failwith("...it works now... ??")
    };
    print_endline("lesgo");
    let s = string_of_action_list_list(prefix);
    _write_string_to_file("prefix.txt", s);
    let _ = totally_minimize(prefix);
    true;
  };

  if (fuel < 0) {
    print_endline("no counterexample found.");
    false;
  } else {
    let actions = Hazelnut_lib.Actions_random.random_action_segment();
    let len = 1 + List.length(rev_acc);
    if (len mod 1000 != 0) {
      // print_endline("trying " ++ string_of_int(len));
      switch (apply_actions(actions, s_acc)) {
      | exception _ =>
        deal_with_countexample(List.rev([actions, ...rev_acc]))
      | s_acc' =>
        generate_minimal_counterexample(
          fuel - 1,
          s_acc',
          [actions, ...rev_acc],
        )
      };
    } else {
      print_endline("trying " ++ string_of_int(len));
      switch (apply_actions_and_test(actions, s_acc)) {
      //(apply_actions_and_test(actions, s)) {
      | exception _ =>
        deal_with_countexample(List.rev([actions, ...rev_acc]))
      // if it succeeds, continue adding random actions
      | s_acc' =>
        generate_minimal_counterexample(
          fuel - 1,
          s_acc',
          [actions, ...rev_acc],
        )
      };
    };
  };
};

let rec generate_minimal_counterexamples = () => {
  let found = generate_minimal_counterexample(30000, initial_state(), []);
  if (!found) {
    generate_minimal_counterexamples();
  };
};

let minimize_prefix = () => {
  let ic = open_in(current_path ++ "/prob_minimized.txt");
  print_endline("parsing...");
  let _ = input_char(ic); // [
  let prefix = test_action_list_sequence(ic, []);
  let prefix = List.concat(prefix);
  print_endline("this better fail...");
  switch (test_actionses([prefix], ())) {
  | exception _ => ()
  | _ => failwith("...it works now... ??")
  };
  print_endline("lesgo");

  print_endline("minimizing...");
  let prob_minimized = little_probabilistic_minimizer(100, prefix);
  let minimized_actions = remove_little_actions_until_cant(prob_minimized);
  // let minimized_actions = Option.get(find_best_failing_subset([], prefix));
  let s = string_of_action_list_list([minimized_actions]);
  _write_string_to_file("more_minimized.txt", s);
  ();
};

let random_action_segments = Hazelnut_lib.Actions_random.random_action_segments;

let boolean_test = actionses => {
  switch (test_actionses(actionses, ())) {
  | exception _ => false
  | () => true
  };
};

let test_indepedence = () => (); /*{ 
  /**
  let actionses = random_action_segments(100000);
  let iterations = List.init(5, _ => boolean_test(actionses));
  assert(
    List.for_all(x => x, iterations) || List.for_all(x => !x, iterations),
  );
   */
};*/

let multi_test_indepedence = () => {
  let _ = List.init(10, _ => test_indepedence());
  ();
};

let oneK_squared = () => () /* {
  /**let _ =
    List.init(10, _ => test_actionses(random_action_segments(1000000)));
  ();*/
};*/

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
  ("minimized", `Quick, test_actionses(minimized_test)),
  ("minimized 2", `Quick, test_actionses(minimized_2)),
  ("minimized 3", `Quick, test_actionses(minimized_3)),
  ("minimized 4", `Quick, test_actionses(minimized_4)),
  ("minimized 5", `Quick, test_actionses(minimized_5)),
  // ("minimized 6", `Quick, test_actionses(minimized_6)),
  ("all", `Quick, test_actionses_all),
  // ("random 1K", `Quick, test_actionses(random_action_segments(1000))),
  // ("random 1K by 1K", `Quick, oneK_squared),
  ("random 10K", `Quick, test_actionses(random_action_segments(10000))),
  // ("random 100K", `Quick, test_actionses(random_action_segments(100000))),
  // ("random 1M", `Quick, test_actionses(random_action_segments(1000000))),
  // ("random 10M", `Quick, test_actionses(random_action_segments(10000000))),
  ("always_fails", `Quick, () => assert(false)) // this is here so that the test libary doesn't stop checking just because everything passed once
];

// generate_minimal_counterexamples();
// minimize_prefix();
// let validity_tests = [];
let validity_tests = actual_tests;

// print_endline("testing");
// let s = initial_state();
// let s' = apply_actions(minimized_5, s);
// all_update_steps(s');
// switch (marked_correctly(s'.ephemeral.root.root_child)) {
// | Some(_) => failwith("marked incorrectly (top test validity)")
// | None => print_endline("marked correctly (top test validity)")
// };
