open Sexplib.Std;
open Hazelnut;
open Order;
open Tree;

module InQueue = {
  [@deriving sexp]
  type upper = {
    mutable syn: bool,
    mutable ann: bool,
    mutable asc: bool,
    mutable list_rec: bool,
    mutable y: bool,
    mutable ite: bool,
    mutable typ_ap: bool,
  };

  [@deriving sexp]
  type lower = {mutable ana: bool};

  [@deriving sexp]
  type root = {mutable ana: bool};

  let default_lower = (): lower => {ana: false};
  let default_root = (): root => {ana: false};
  let default_upper = (): upper => {
    syn: false,
    asc: false,
    ann: false,
    list_rec: false,
    y: false,
    ite: false,
    typ_ap: false,
  };
};

module BinderKind = {
  [@deriving (sexp, compare)]
  type t =
    | Lam
    | TypFun;
};

module Iexp = {
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

  let add_bound_var = (var: upper, bound_vars: var_set) => {
    let (left, right) = var.interval;
    // Order.lt(left, right) ? () : failwith("bad interval");
    // print_endline(
    //   "Adding bound var with left endpoint: "
    //   ++ string_of_sexp(Order.sexp_of_t(left))
    //   ++ " and right endpoint "
    //   ++ string_of_sexp(Order.sexp_of_t(right)),
    // );
    bound_vars.contents = Tree.insert(var, left, right, bound_vars.contents);
  };

  let remove_bound_var = (var: upper, bound_vars: var_set) => {
    // print_endline(
    //   "Removing bound var with left endpoint: "
    //   ++ string_of_sexp(Order.sexp_of_t(fst(var.interval)))
    //   ++ " and right endpoint "
    //   ++ string_of_sexp(Order.sexp_of_t(snd(var.interval))),
    // );
    bound_vars.contents =
      Tree.delete(fst(var.interval), bound_vars.contents);
  };

  let excise_bound_vars = (interval: (Order.t, Order.t), bound_vars: var_set) => {
    // Order.lt(fst(interval), snd(interval)) ? () : failwith("bad interval");
    // print_endline(
    //   "Excising range: "
    //   ++ string_of_sexp(Order.sexp_of_t(fst(interval)))
    //   ++ " and right endpoint "
    //   ++ string_of_sexp(Order.sexp_of_t(snd(interval))),
    // );
    let (remaining, excised) =
      Tree.excise_interval(interval, bound_vars.contents);
    bound_vars.contents = remaining;
    excised;
  };

  let union_bound_vars = (vars: Tree.t(upper), bound_vars: var_set) => {
    bound_vars.contents = Tree.union((vars, bound_vars.contents));
  };
};

let child_of_parent = (p: Iexp.parent): Iexp.upper => {
  switch (p) {
  | Deleted => failwith("child of deleted")
  | Root(r) => r.root_child
  | Lower(r) => r.child
  };
};

// let initial_om = Order.create();
// let initial_interval = (initial_om, Order.add_next(initial_om));

let exp_hole_upper = (i: (Order.t, Order.t)): Iexp.upper => {
  parent: Deleted,
  syn: Some(Hole),
  interval: i,
  in_queue_upper: InQueue.default_upper(),
  middle: EHole,
  deleted_upper: false,
};

let dummy_upper = () => {
  let a = Order.create();
  let b = Order.add_next(a);
  exp_hole_upper((a, b));
};
