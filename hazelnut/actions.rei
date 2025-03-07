// open Hazelnut;
// open Incremental;
open State;

module Child: {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two
    | Three;
};

module Iaction: {
  [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(Child.t)
    | Delete
    | WrapArrow(Child.t)
    | InsertNumType
    | InsertNumLit(int)
    | InsertVar(string)
    | WrapPlus(Child.t)
    | WrapAp(Child.t)
    | WrapProduct(Child.t)
    | WrapLam
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

let apply_action: (Istate.t, Iaction.t) => Istate.t;
let apply_actions: (list(Iaction.t), Istate.t) => Istate.t;
