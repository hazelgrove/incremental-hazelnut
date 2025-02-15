open Hazelnut;

// module Ityp: {
//   [@deriving sexp]
//   type lower = {
//     mutable upper,
//     mutable child: upper,
//   }

//   and middle =
//     | Arrow(lower, lower)
//     | Num
//     | Hole

//   and upper = {
//     mutable parent: option(lower),
//     mutable is_new: bool,
//     middle,
//   };
// };

module Iexp: {
  [@deriving sexp]
  type lower = {
    mutable upper,
    ana: option(Htyp.t),
    mutable marked: bool,
    mutable child: upper,
  }

  and middle =
    | Var(string, bool, binder)
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(string, ref(Htyp.t), bool, bool, lower, bound_vars)
    | Ap(lower, bool, lower)
    | Asc(lower, ref(Htyp.t))
    | EHole

  and upper = {
    mutable parent,
    syn: option(Htyp.t),
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
    | WrapLam(string)
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

module Update: {
  [@deriving sexp]
  type t =
    | NewSyn(Iexp.upper)
    | NewAna(Iexp.lower)
    | NewAnn(Iexp.upper)
    | NewAsc(Iexp.upper);
};

module UpdateQueue: {
  [@deriving sexp]
  type t = list(Update.t);
};

module Icursor: {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t);
};

module Istate: {
  [@deriving sexp]
  type t = (Icursor.t, UpdateQueue.t);
};

let initial_root: Iexp.parent;
let initial_state: Istate.t;
let hexp_of_iexp: Iexp.upper => Hexp.t;
let pexp_of_iexp: (Iexp.upper, Istate.t) => Pexp.t;
let apply_action: (Istate.t, Iaction.t) => Istate.t;
