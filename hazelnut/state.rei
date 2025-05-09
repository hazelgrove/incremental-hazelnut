open Hazelnut;
open Incremental;
open UpdateQueue;
open Tree;

module Icursor: {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t)
    | CursorBind(Iexp.upper);
};

module BinderSet: {
  type t = Hashtbl.t((string, BinderKind.t), Tree.t(Iexp.upper));
};

module Istate: {
  [@deriving sexp]
  type ephemeral = {
    root: Iexp.root,
    q: UpdateQueue.t,
    binder_set: BinderSet.t,
  };
  [@deriving sexp]
  type persistent = {c: Icursor.t};
  [@deriving sexp]
  type t = {
    ephemeral,
    persistent,
  };
};

let initial_state: unit => Istate.t;
