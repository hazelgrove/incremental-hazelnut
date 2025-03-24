open Hazelnut;
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
    | InsertBoolType
    | InsertUnitType
    | InsertLt
    | InsertITE
    | InsertList
    | InsertNumLit(int)
    | InsertVar(string)
    | InsertNil
    | InsertCons
    | InsertListRec
    | InsertListMatch
    | InsertY
    | WrapPlus(Child.t)
    | WrapAp(Child.t)
    | WrapPair(Child.t)
    | WrapProduct(Child.t)
    | WrapProj(ProdSide.t)
    | WrapLam
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

let apply_action: (Istate.t, Iaction.t) => Istate.t;
let apply_actions: (list(Iaction.t), Istate.t) => Istate.t;
