open Id;
open Typ;
open Mark;
open Tree;
open Order;
open Patch;

module Node = {
  type pat_constructor =
    | Var(string);

  type typ_constructor =
    | Arrow;

  type var_data = Id.t;

  type fun_data = ref(Tree.t(Id.t));

  type exp_constructor =
    | Var(var_data, string)
    | Fun(fun_data, string)
    | Ap;

  type exp_data = {
    mutable ana: option(Typ.t),
    mutable mark_consistent: Mark.t,
    // mutable dirty: bool,
    mutable syn: option(Typ.t),
  };

  type typ_data = {
    // future optimization: store ADT of self
    // mutable pure_typ: Typ.t,
    mutable dirty: bool,
  };

  type content =
    | Root
    | Pat(pat_constructor)
    | Typ(typ_data, typ_constructor)
    | Exp(exp_data, exp_constructor);

  type position = int;

  type edge = {
    id: Id.t,
    source: (Id.t, position),
    destination: Id.t,
    sign: Patch.sign,
    meta: Patch.meta,
  };

  type edge_set = list(edge)

  // future optimization: store visible parents and children using refs,
  // rather than our own indirect Id.t based references

  and t = {
    id: Id.t,
    interval: (Order.t, Order.t),
    mutable deleted: bool,
    mutable root: bool,
    mutable part_of_unicycle: bool,
    mutable parent_edges: edge_set, // live incoming edges
    // mutable parent: option((t, position)),
    mutable content,
    mutable children_edges: list(edge_set), // live outgoing edges at each position
    // mutable children: list(t),
    mutable marks: list(Mark.t),
  };

  let create_node = (id: Id.t, content: content): t => {
    let initial_order = Order.create();
    let initial_interval = (initial_order, Order.add_next(initial_order));
    {
      id,
      interval: initial_interval,
      deleted: false,
      root: true,
      part_of_unicycle: false,
      parent_edges: [],
      content,
      children_edges: [],
      marks: [],
    };
  };

  let initial = (counter: Id.counter): t => {
    create_node(Id.fresh(counter), Root);
  };

  let get_typ_data = (e: t): typ_data => {
    switch (e.content) {
    | Typ(typ_data, _) => typ_data
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
    | Exp(exp_data, _) => exp_data
    | Root
    | Typ(_)
    | Pat(_) => failwith("Get exp_data of non exp")
    };
  };

  let get_syn = (e: t): option(Typ.t) => {
    get_exp_data(e).syn;
  };

  let get_ana = (e: t): option(Typ.t) => {
    get_exp_data(e).ana;
  };
  let set_syn = (e: t, syn: option(Typ.t)) => {
    get_exp_data(e).syn = syn;
  };
  let set_ana = (e: t, ana: option(Typ.t)) => {
    get_exp_data(e).ana = ana;
  };
};

let first: list('a) => 'a = List.nth(_, 0);
let second: list('a) => 'a = List.nth(_, 1);
let third: list('a) => 'a = List.nth(_, 2);
