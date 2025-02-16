module type Comparable = {
  [@deriving sexp]
  type t;
  let eq: (t, t) => bool;
  let leq: (t, t) => bool;
};

module PQueue:
  (Elem: Comparable) =>
   {
    [@deriving sexp]
    type t;

    let empty: t;
    let push: (Elem.t, t) => t;
    let push_list: (list(Elem.t), t) => t;
    let pop: t => option((Elem.t, t));
    let list_of_t: t => list(Elem.t);
  };
