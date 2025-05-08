open Id;
open Typ;
open Mark;
open Order;

module Term = {
  type edge = int; // todo - should include edge state, id, and metadata I think

  type typ_constructor =
    | Hole
    | Arrow;

  type pat_constructor =
    | Hole
    | Var(string);

  type exp_constructor =
    | Var(string)
    | Fun(string) //, bound_var_set)
    | Ap
    | Hole
    | Multihole
    | Multiref(Id.t)
    | Uniref(Id.t);

  type constructor =
    | Typ(typ_constructor)
    | Pat(pat_constructor)
    | Exp(exp_constructor);

  type dirtyTyp = (option(Typ.t), bool);

  type exp_data = {
    mutable ana: dirtyTyp,
    mutable mark_consistent: Mark.t,
    mutable syn: dirtyTyp,
  };

  type typ_data = {
    // ADT of self
    pure_typ: option(Typ.t),
    // only for root of types, whether self is dirty
    mutable dirty: bool,
  };

  type t = {
    id: Id.t,
    interval: (Order.t, Order.t),
    deleted: bool,
    // upper data
    mutable parent: option(t),
    edges: list(edge),
    exp_data: option(exp_data),
    typ_data: option(typ_data),
    // mid/lower data
    constructor,
    children: list(t),
    marks: list(Mark.t),
  };

  let initial = (): t => {
    let initial_order = Order.create();
    let initial_interval = (initial_order, Order.add_next(initial_order));
    let initial_exp_data = {
      ana: (None, false),
      mark_consistent: Unmarked,
      syn: (Some(Hole), false),
    };
    {
      id: 0,
      interval: initial_interval,
      deleted: false,
      parent: None,
      edges: [],
      exp_data: Some(initial_exp_data),
      typ_data: None,
      constructor: Exp(Hole),
      children: [],
      marks: [],
    };
  };

  let get_syn = (e: t): dirtyTyp => {
    Option.get(e.exp_data).syn;
  };
  let get_ana = (e: t): dirtyTyp => {
    Option.get(e.exp_data).ana;
  };
  let set_syn = (e: t, syn: dirtyTyp) => {
    Option.get(e.exp_data).syn = syn;
  };
  let set_ana = (e: t, ana: dirtyTyp) => {
    Option.get(e.exp_data).ana = ana;
  };
};
