open Id;
open Typ;
open Mark;
open Order;

module Term = {
  type edge = unit; // todo - should include edge state, id, and metadata I think

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
    | Multihole(int) // number of children
    | Multiref(Id.t)
    | Uniref(Id.t);

  let arity =
    fun
    | Var(_) => (1, 1) // variable has a type child, the type of the var
    | Fun(_) => (2, 2)
    | Ap => (2, 1)
    | Hole => (0, 0)
    | Multihole(n) => (n, 0)
    | Multiref(_) => (0, 0)
    | Uniref(_) => (0, 0);

  type dirtyTyp = (option(Typ.t), bool);

  type exp_data = {
    mutable ana: dirtyTyp,
    mutable mark_consistent: Mark.t,
    mutable syn: dirtyTyp,
  };

  type typ_data = {
    // ADT of self
    mutable pure_typ: Typ.t,
    // only for root of types, whether self is dirty
    mutable dirty: bool,
  };

  type content =
    | Typ(typ_constructor, typ_data)
    | Pat(pat_constructor)
    | Exp(exp_constructor, exp_data);

  type t = {
    id: Id.t,
    interval: (Order.t, Order.t),
    deleted: bool,
    mutable parent: option(t),
    edges: list(edge),
    content,
    children: list(t),
    mutable marks: list(Mark.t),
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
      content: Exp(Hole, initial_exp_data),
      children: [],
      marks: [],
    };
  };

  let get_typ_data = (e: t): typ_data => {
    switch (e.content) {
    | Typ(_, typ_data) => typ_data
    | _ => failwith("Get typ_data of non typ")
    };
  };

  let get_typ_dirtiness = (e: t) => {
    get_typ_data(e).dirty;
  };

  let set_typ_dirtiness = (e: t, b: bool) => {
    get_typ_data(e).dirty = b;
  };

  let get_exp_data = (e: t): exp_data => {
    switch (e.content) {
    | Exp(_, exp_data) => exp_data
    | Typ(_)
    | Pat(_) => failwith("Get exp_data of non exp")
    };
  };

  let get_syn = (e: t): dirtyTyp => {
    get_exp_data(e).syn;
  };

  let get_ana = (e: t): dirtyTyp => {
    get_exp_data(e).ana;
  };
  let set_syn = (e: t, syn: dirtyTyp) => {
    get_exp_data(e).syn = syn;
  };
  let set_ana = (e: t, ana: dirtyTyp) => {
    get_exp_data(e).ana = ana;
  };
};

let first: list('a) => 'a = List.nth(_, 0);
let second: list('a) => 'a = List.nth(_, 1);
let third: list('a) => 'a = List.nth(_, 2);
