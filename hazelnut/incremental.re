open Sexplib.Std;
open Hazelnut;
open Order;
// open Queue;
// open Monad_lib.Monad;

module InQueue = {
  [@deriving sexp]
  type upper = {
    mutable syn: bool,
    mutable ann: bool,
    mutable asc: bool,
  };

  [@deriving sexp]
  type lower = {mutable ana: bool};

  [@deriving sexp]
  type root = {mutable ana: bool};

  let default_lower = (): lower => {ana: false};

  let default_root = (): root => {ana: false};

  let default_upper = (): upper => {syn: false, asc: false, ann: false};
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

  let add_bound_var = (var: upper, bound_vars: bound_vars) => {
    bound_vars.contents = [var, ...bound_vars.contents];
  };

  let remove_bound_var = (var: upper, bound_vars: bound_vars) => {
    bound_vars.contents =
      List.filter(var' => var !== var', bound_vars.contents);
  };
};

let child_of_parent = (p: Iexp.parent): Iexp.upper => {
  switch (p) {
  | Deleted => failwith("child of deleted")
  | Root(r) => r.root_child
  | Lower(r) => r.child
  };
};

let initial_om = Order.create();
let initial_interval = (initial_om, Order.add_next(initial_om));

let exp_hole_upper = (i: (Order.t, Order.t)): Iexp.upper => {
  parent: Deleted,
  syn: Some(Hole),
  interval: i,
  in_queue_upper: InQueue.default_upper(),
  middle: EHole,
  deleted_upper: false,
};

let dummy_upper = exp_hole_upper(initial_interval);

let var_syn = (e: Iexp.upper, syn: Htyp.t) => {
  switch (e.middle) {
  | Var(_) => e.syn = Some(syn)
  | _ => failwith("var_syn called on non-var")
  };
};
