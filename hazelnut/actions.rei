open State;

type child = int;

module Action: {
  // [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(child)
    | Delete
    | WrapArrow(child)
    | InsertVar(string)
    | WrapLam
    | WrapAp(child)
    | Unwrap(child);
};

let apply_action: (State.t, Action.t) => State.t;
let apply_actions: (list(Action.t), State.t) => State.t;
