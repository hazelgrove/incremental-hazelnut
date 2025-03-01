open Hazelnut;
open Order;

module InQueue: {
  type upper = {
    mutable syn: bool,
    mutable ann: bool,
    mutable asc: bool,
  };
  type lower = {mutable ana: bool};
  type root = {mutable ana: bool};

  let default_lower: unit => lower;
  let default_root: unit => root;
  let default_upper: unit => upper;
};

module Iexp: {
  [@deriving sexp]
  type lower = {
    mutable upper,
    mutable ana: option(Htyp.t),
    mutable marked: Mark.t,
    mutable child: upper,
    in_queue_lower: InQueue.lower,
    mutable deleted_lower: bool,
  }

  and middle =
    | Var(string, ref(Mark.t), ref(binder))
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(
        ref(Bind.t),
        ref(Htyp.t),
        ref(Mark.t),
        ref(Mark.t),
        lower,
        bound_vars,
      )
    | Ap(lower, ref(Mark.t), lower)
    | Asc(lower, ref(Htyp.t))
    | EHole

  and upper = {
    mutable parent,
    mutable syn: option(Htyp.t),
    middle,
    mutable interval: (Order.t, Order.t),
    in_queue_upper: InQueue.upper,
    mutable deleted_upper: bool,
  }

  and root = {
    mutable root_child: upper,
    in_queue_root: InQueue.root,
  }

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(root) // root of the main program
    | Lower(lower) // child location of a constuctor

  and binder = parent // pointer from a variable occurrence to binding location
  and bound_vars = ref(list(upper)); // pointers from a binder to the variable occurrences it binds

  let add_bound_var: (upper, bound_vars) => unit;
  let remove_bound_var: (upper, bound_vars) => unit;
};

let child_of_parent: Iexp.parent => Iexp.upper;

let initial_interval: (Order.t, Order.t);
let exp_hole_upper: ((Order.t, Order.t)) => Iexp.upper;
let dummy_upper: Iexp.upper;

let var_syn: (Iexp.upper, Htyp.t) => unit;
