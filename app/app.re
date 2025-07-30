open Core;
open Incr_dom;
open Monad_lib.Monad;
open Hazelnut_lib.Hazelnut;
open Hazelnut_lib.State;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Update;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Marking;

[@deriving (sexp, fields)]
type state = {
  istate: Istate.t,
  // t: Htyp.t,
  warning: option(string),
  var_input: string,
  typvar_input: string,
  let_input: string,
  lit_input: string,
  bool_input: string,
  action_string: string,
  vizbit: bool,
};

let _ = Hazelnut_lib.Order.Order.create();

// let s = initial_state();
// let initial_istate = apply_actions(minimized_5, s);
// all_update_steps(initial_istate);
// switch (marked_correctly(initial_istate.ephemeral.root.root_child)) {
// | Some(_) => failwith("marked incorrectly (top level app)")
// | None => print_endline("marked correctly (top level app)")
// };
// let apply_actions_and_test = (actions, s) => {
//   let s' = apply_actions(actions, s);
//   all_update_steps(s');
//   switch (marked_correctly(s'.ephemeral.root.root_child)) {
//   | Some(e') =>
//     print_endline("failed test");
//     print_endline("ERROR: see:");
//     print_endline(
//       string_of_pexp(pexp_of_iexp(s'.ephemeral.root.root_child, s')),
//     );
//     print_endline("should see:");
//     print_endline(string_of_pexp(pexp_of_iexp(e', s')));
//     failwith("failed test");
//   | None => ()
//   };
//   s';
// };

// let rec test_actionses_rec = (actionses: list(list(Iaction.t)), s) => {
//   switch (actionses) {
//   | [] =>
//     all_update_steps(s);
//     switch (marked_correctly(s.ephemeral.root.root_child)) {
//     | Some(e') =>
//       print_endline("failed test");
//       print_endline("ERROR: see:");
//       print_endline(
//         string_of_pexp(pexp_of_iexp(s.ephemeral.root.root_child, s)),
//       );
//       print_endline("should see:");
//       print_endline(string_of_pexp(pexp_of_iexp(e', s)));
//       failwith("failed test");
//     | None => ()
//     };
//   | [actions, ...actionses] =>
//     let s' = apply_actions(actions, s);
//     test_actionses_rec(actionses, s');
//   };
// };

// let test_actionses = (actionses: list(list(Iaction.t)), ()) => {
//   let s = initial_state();
//   test_actionses_rec(actionses, s);
//   // print_endline("all tests done.");
// };

// let random_action_segments = Hazelnut_lib.Actions_random.random_action_segments;

// test_actionses(random_action_segments(10000000));
// print_endline("testin done app 10M");

let _minimized_6: list(Iaction.t) = [
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
];

module Model = {
  [@deriving (sexp, fields)]
  type t = {state};

  let set = (s: state): t => {state: s};

  let init = (): t => {
    let s = initial_state();
    let initial_istate = s; //apply_actions(minimized_6, s);
    // all_update_steps(initial_istate);
    // switch (marked_correctly(initial_istate.ephemeral.root.root_child)) {
    // | Some(_) => failwith("marked incorrectly (init app)")
    // | None => print_endline("marked correctly (init app)")
    // };
    set({
      istate: initial_istate,
      // t: Hole,
      warning: None,
      var_input: "",
      typvar_input: "",
      let_input: "",
      lit_input: "",
      bool_input: "true | false",
      action_string: "",
      vizbit: false // meaningless, flipped so that the display updates
    });
  };
  // let cutoff = (t1: t, t2: t): bool => compare(t1, t2) == 0;
  let cutoff = (_: t, _: t): bool => false;
};

module Action = {
  [@deriving sexp]
  type input_location =
    | Var
    | TypVar
    | Let
    | NumLit
    | BoolLit;

  [@deriving sexp]
  type action =
    | HazelnutAction(Iaction.t)
    | UpdateStep
    | UpdateStepOut
    | UpdateInput(input_location, string)
    | ShowWarning(string);

  [@deriving sexp]
  type t = list(action);
};

module State = {
  type t = unit;
};

let apply_action =
    (model: Model.t, actions: Action.t, _, ~schedule_action as _): Model.t => {
  let f = (model: Model.t, action: Action.action): Model.t => {
    let state = model.state;

    let warn = (warning: string): Model.t =>
      Model.set({...state, warning: Some(warning)});

    let marking_validate = () =>
      switch (marked_correctly(state.istate.ephemeral.root.root_child)) {
      | None => print_endline("marking correct")
      | Some(e') =>
        print_endline("ERROR: see:");
        print_endline(
          string_of_pexp(
            pexp_of_iexp(
              state.istate.ephemeral.root.root_child,
              state.istate,
            ),
          ),
        );
        print_endline("should see:");
        print_endline(string_of_pexp(pexp_of_iexp(e', state.istate)));
        failwith("Marking failure");
      };

    switch (action) {
    | HazelnutAction(action) =>
      try({
        let istate' = apply_action(state.istate, action);
        let action_string =
          state.action_string ++ string_of_action(action) ++ ",";
        Model.set({...state, action_string, istate: istate'});
      }) {
      | Unimplemented => warn("Unimplemented")
      }
    | UpdateStepOut =>
      all_update_steps(state.istate);
      marking_validate();
      Model.set({...state, vizbit: !state.vizbit});
    | UpdateStep =>
      let _ = update_step(state.istate);
      Model.set({...state, vizbit: !state.vizbit});
    | UpdateInput(Var, var_input) => Model.set({...state, var_input})
    | UpdateInput(TypVar, typvar_input) => Model.set({...state, typvar_input})
    | UpdateInput(Let, let_input) => Model.set({...state, let_input})
    | UpdateInput(NumLit, lit_input) => Model.set({...state, lit_input})
    | UpdateInput(BoolLit, bool_input) => Model.set({...state, bool_input})
    | ShowWarning(warning) => Model.set({...state, warning: Some(warning)})
    };
  };

  List.fold_left(actions, ~init=model, ~f);
};

let on_startup = (~schedule_action as _, _) => Async_kernel.return();

let view =
    (m: Incr.t(Model.t), ~inject: Action.t => Ui_effect.t(Base.unit))
    : Ui_incr.t(Vdom.Node.t) => {
  open Incr.Let_syntax;
  open Vdom;
  let%map body = {
    let%map state = m >>| Model.state;

    // let e_cursor = state.e;

    // let e_no_cursor = erase_exp(e_cursor);

    // let (e_marked, t) =
    //   mark_syn(TypCtx.empty, e_no_cursor);

    // let e_folded = fold_zexp_mexp(e_cursor, e_marked);
    let root_display_exp = pexp_of_root(state.istate);

    let root_string = string_of_pexp(root_display_exp);

    let expression =
      Node.div([
        Node.p([Node.textf("%s", root_string)]),
        // Node.p([Node.textf("%s", string_of_pexp(pexp_of_htyp(t)))]),
      ]);
    print_endline(root_string);

    let buttons = {
      let button =
          (
            label: string,
            action: Action.action,
            input: option((Action.input_location, string)),
          )
          : Node.t => {
        let button_node = {
          let actions =
            switch (input) {
            | Some((input_location, _)) => [
                action,
                Action.UpdateInput(input_location, ""),
              ]
            | None => [action]
            };

          Node.button(
            ~attrs=[Attr.on_click(_ev => inject(actions))],
            [Node.text(label)],
          );
        };

        let input_node = {
          let+ (input_location, input_value) = input;
          Node.input(
            ~attrs=[
              Attr.type_("text"),
              Attr.string_property("value", input_value),
              Attr.on_input((_ev, text) =>
                inject([Action.UpdateInput(input_location, text)])
              ),
            ],
            (),
          );
        };

        Node.div(
          switch (input_node) {
          | Some(input_node) => [button_node, input_node]
          | None => [button_node]
          },
        );
      };

      let update_buttons =
        Node.div([
          button("Update Step", Action.UpdateStep, None),
          button("All Update Steps", Action.UpdateStepOut, None),
        ]);

      let move_buttons =
        Node.div([
          button("Move to Parent", Action.HazelnutAction(MoveUp), None),
          button(
            "Move to Child 1",
            Action.HazelnutAction(MoveDown(One)),
            None,
          ),
          button(
            "Move to Child 2",
            Action.HazelnutAction(MoveDown(Two)),
            None,
          ),
          button(
            "Move to Child 3",
            Action.HazelnutAction(MoveDown(Three)),
            None,
          ),
        ]);

      let construct_buttons =
        Node.div([
          button(
            "Wrap Arrow (Left)",
            Action.HazelnutAction(WrapArrow(One)),
            None,
          ),
          button(
            "Wrap Arrow (Right)",
            Action.HazelnutAction(WrapArrow(Two)),
            None,
          ),
          button(
            "Construct Num Type",
            Action.HazelnutAction(InsertNumType),
            None,
          ),
          button(
            "Construct List Type",
            Action.HazelnutAction(InsertList),
            None,
          ),
          button(
            "Construct Var",
            Action.HazelnutAction(InsertVar(state.var_input)),
            Some((Var, state.var_input)),
          ),
          button("Wrap Lambda", Action.HazelnutAction(WrapLam), None),
          button("Wrap Ap (Fun)", Action.HazelnutAction(WrapAp(One)), None), // input needed here? or some cursor needed
          button("Wrap Ap (Arg)", Action.HazelnutAction(WrapAp(Two)), None),
          button(
            "Wrap Pair (Left)",
            Action.HazelnutAction(WrapPair(One)),
            None,
          ),
          button(
            "Wrap Pair (Right)",
            Action.HazelnutAction(WrapPair(Two)),
            None,
          ),
          button(
            "Wrap Product (Left)",
            Action.HazelnutAction(WrapProduct(One)),
            None,
          ),
          button(
            "Wrap Product (Right)",
            Action.HazelnutAction(WrapProduct(Two)),
            None,
          ),
          button(
            "Wrap Proj (Fst)",
            Action.HazelnutAction(WrapProj(Fst)),
            None,
          ),
          button(
            "Wrap Proj (Snd)",
            Action.HazelnutAction(WrapProj(Snd)),
            None,
          ),
          button("Wrap Asc", Action.HazelnutAction(WrapAsc), None),
          button(
            "Construct Num Lit",
            try(
              Action.HazelnutAction(
                InsertNumLit(int_of_string(state.lit_input)),
              )
            ) {
            | Failure(_) => Action.ShowWarning("Invalid input")
            },
            Some((NumLit, state.lit_input)),
          ),
          button(
            "Wrap Plus (Left)",
            Action.HazelnutAction(WrapPlus(One)),
            None,
          ),
          button(
            "Wrap Plus (Right)",
            Action.HazelnutAction(WrapPlus(Two)),
            None,
          ),
          button("Insert Nil", Action.HazelnutAction(InsertNil), None),
          button("Insert Cons", Action.HazelnutAction(InsertCons), None),
          button(
            "Insert ListRec",
            Action.HazelnutAction(InsertListRec),
            None,
          ),
          button("Insert Y", Action.HazelnutAction(InsertY), None),
          button(
            "Construct TypVar",
            Action.HazelnutAction(InsertTypVar(state.var_input)),
            Some((TypVar, state.var_input)),
          ),
          button(
            "WrapTypFun",
            Action.HazelnutAction(WrapTypFun),
            None,
          ),
          button(
            "WrapTypAp",
            Action.HazelnutAction(WrapTypAp),
            None,
          ),
          button(
            "WrapForAll",
            Action.HazelnutAction(WrapForAll),
            None,
          ),
        ]);

      let unwrap_buttons =
        Node.div([
          button("Unwrap", Action.HazelnutAction(Unwrap(One)), None),
          button(
            "Unwrap (Right)",
            Action.HazelnutAction(Unwrap(Two)),
            None,
          ),
        ]);

      let delete_button =
        Node.div([button("Delete", Action.HazelnutAction(Delete), None)]);

      Node.div([
        update_buttons,
        move_buttons,
        construct_buttons,
        unwrap_buttons,
        delete_button,
      ]);
    };

    let warning =
      Node.p(
        switch (state.warning) {
        | Some(warning) => [Node.text(warning)]
        | None => []
        },
      );

    let action_string =
      Node.div([
        Node.p([Node.textf("%s", "[" ++ state.action_string ++ "]")]),
      ]);

    Node.div([expression, buttons, action_string, warning]);
  };

  Node.body([body]);
};

let create = (model, ~old_model as _, ~inject) => {
  open Incr.Let_syntax;
  let%map apply_action = {
    let%map model = model;
    apply_action(model);
  }
  and view = view(model, ~inject)
  and model = model;
  Component.create(~apply_action, model, view);
};

let initial_model = Model.init();
