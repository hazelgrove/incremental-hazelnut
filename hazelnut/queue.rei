module type Comparable = {
  [@deriving sexp]
  type t;
  let leq: (t, t) => bool;
};

module PQueue:
  (Elem: Comparable) =>
   {
    [@deriving sexp]
    type t;

    let empty: unit => t;
    let push: (Elem.t, t) => unit;
    let pop: t => option(Elem.t);
    let list_of_t: t => list(Elem.t);
  };
