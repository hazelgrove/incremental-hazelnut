open Typ;
open Term;

module Update: {
  type t =
    | NewSyn(Term.t)
    | NewAna(Term.t)
    | NewTyp(Term.t);
  let leq: (t, t) => bool;
};

module UpdateQueue: {
  // [@deriving sexp]
  type t;

  let empty: unit => t;
  let list_of_t: t => list(Update.t);
  let update_push: (Update.t, t) => unit;
  let update_push_list: (list(Update.t), t) => unit;

  let update_pop: t => option(Update.t);

  let update_ana: (Term.t, option(Typ.t)) => list(Update.t);
  let update_syn: (Term.t, option(Typ.t)) => list(Update.t);
};
