open Incremental;

module Update: {
  type t =
    | NewSyn(Iexp.upper)
    | NewAna(Iexp.parent)
    | NewAnn(Iexp.upper)
    | NewAsc(Iexp.upper);
  let leq: (t, t) => bool;
};

module UpdateQueue: {
  [@deriving sexp]
  type t;

  let empty: t;
  let list_of_t: t => list(Update.t);
  let update_push: (Update.t, t) => t;
  let update_push_list: (list(Update.t), t) => t;

  type pop_result =
    | Empty
    | Flushed(t)
    | Pops(Update.t, t);
  let update_pop: t => pop_result;
};
