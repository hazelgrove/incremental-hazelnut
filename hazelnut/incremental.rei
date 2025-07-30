open Hazelnut;
open Order;
open Tree;

module InQueue: {
  type upper = {
    mutable syn: bool,
    mutable ann: bool,
    mutable asc: bool,
    mutable list_rec: bool,
    mutable y: bool,
    mutable ite: bool,
    mutable typ_ap: bool,
  };
  type lower = {mutable ana: bool};
  type root = {mutable ana: bool};

  let default_lower: unit => lower;
  let default_root: unit => root;
  let default_upper: unit => upper;
};

module BinderKind: {
  [@deriving (sexp, compare)]
  type t =
    | Lam
    | TypFun;
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
        var_set,
        typ_binders,
      )
    | Ap(lower, ref(Mark.t), lower)
    | Pair(lower, lower, ref(Mark.t))
    | Proj(ProdSide.t, lower, ref(Mark.t))
    | Asc(lower, ref(Htyp.t), typ_binders)
    | Nil
    | Cons
    | ListRec(ref(Htyp.t), typ_binders)
    | Y(ref(Htyp.t), typ_binders)
    | ITE(ref(Htyp.t), typ_binders)
    | TypFun(ref(Bind.t), ref(Mark.t), lower, var_set)
    | TypAp(lower, ref(Mark.t), ref(Htyp.t), typ_binders)
    | EHole

  and upper = {
    mutable parent,
    mutable syn: option(Htyp.t),
    middle,
    interval: (Order.t, Order.t),
    in_queue_upper: InQueue.upper,
    mutable deleted_upper: bool,
  }

  and root = {
    mutable root_child: upper,
    free_vars: Hashtbl.t((string, BinderKind.t), var_set),
    in_queue_root: InQueue.root,
  }

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(root) // root of the main program
    | Lower(lower) // child location of a constuctor

  and binder = parent // pointer from a variable occurrence to binding location
  and var_set = ref(Tree.t(upper)) // pointers from a binder to the variable occurrences it binds
  and typ_binders = Hashtbl.t(string, parent); // stored on the expression immediately containing a type

  let add_bound_var: (upper, var_set) => unit;
  let remove_bound_var: (upper, var_set) => unit;
  let excise_bound_vars: ((Order.t, Order.t), var_set) => Tree.t(upper);
  let union_bound_vars: (Tree.t(upper), var_set) => unit;
};

let child_of_parent: Iexp.parent => Iexp.upper;

// let initial_interval: (Order.t, Order.t);
let exp_hole_upper: ((Order.t, Order.t)) => Iexp.upper;
let dummy_upper: unit => Iexp.upper;
