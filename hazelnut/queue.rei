module type Comparable = {
  type t;
  let leq: (t, t) => bool;
};

module PQueue:
  (Elem: Comparable) =>
   {
    type t;

    let push: (Elem.t, t) => t;
    let pop: t => option((Elem.t, t));
  };
