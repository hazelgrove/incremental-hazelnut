// open Typ;
open Node;

module Update: {
  type t =
    | NewSyn(Node.t)
    | NewAna(Node.t)
    | NewTyp(Node.t);
  let leq: (t, t) => bool;
};

module UpdateQueue: {
  // [@deriving sexp]
  type t;
  let empty: unit => t;
  // let list_of_t: t => list(Update.t);
  // let update_push: (Update.t, t) => unit;
  // let update_push_list: (list(Update.t), t) => unit;
  // let update_pop: t => option(Update.t);
  // let update_ana: (Node.t, option(Typ.t)) => list(Update.t);
  // let update_syn: (Node.t, option(Typ.t)) => list(Update.t);
};
