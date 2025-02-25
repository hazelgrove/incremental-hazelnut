open Hazelnut;
open Incremental;
open UpdateQueue;

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
    | WrapLam
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

module Icursor: {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t)
    | CursorBind(Iexp.upper);
};

module Istate: {
  [@deriving sexp]
  type t = {
    c: Icursor.t,
    q: UpdateQueue.t,
  };
};

let dummy_upper: Iexp.upper;
let initial_root: Iexp.parent;
let initial_state: Istate.t;
let apply_action: (Istate.t, Iaction.t) => Istate.t;
let update_step: Istate.t => option(Istate.t);
let all_update_steps: Istate.t => Istate.t;
