open Hazelnut;
open Total_order;

module Iexp: {
  [@deriving sexp]
  type lower = {
    mutable upper,
    mutable ana: option(Htyp.t),
    mutable marked: Mark.t,
    mutable child: upper,
  }

  and middle =
    | Var(string, Mark.t, binder)
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(Bind.t, ref(Htyp.t), ref(Mark.t), ref(Mark.t), lower, bound_vars)
    | Ap(lower, ref(Mark.t), lower)
    | Asc(lower, ref(Htyp.t))
    | EHole

  and upper = {
    mutable parent,
    mutable syn: option(Htyp.t),
    mutable interval: (T.t, T.t),
    middle,
  }

  and child_ref = {mutable root_child: upper}

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(child_ref) // root of the main program
    | Lower(lower) // child location of a constuctor

  and binder = parent // pointer from a variable occurrence to binding location
  and bound_vars = ref(list(upper)); // pointers from a binder to the variable occurrences it binds
};

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
    | WrapLamInner(Bind.t, Htyp.t, Mark.t, Mark.t)
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

module Update: {
  [@deriving sexp]
  type t =
    | NewSyn(Iexp.upper)
    | NewAna(Iexp.parent)
    | NewAnn(Iexp.upper)
    | NewAsc(Iexp.upper);

  let leq: (t, t) => bool;
};

module UpdateQueue: {
  type t;
  let list_of_t: t => list(Update.t);
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
let child_of_parent: Iexp.parent => Iexp.upper;
let apply_action: (Istate.t, Iaction.t) => Istate.t;
let update_step: Istate.t => option(Istate.t);
let all_update_steps: Istate.t => Istate.t;
