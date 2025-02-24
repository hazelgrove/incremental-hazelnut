open Sexplib.Std;

// http://courses.cms.caltech.edu/cs11/material/ocaml/lab4/lab4.html

// this is a min-heap

module type Comparable = {
  [@deriving sexp]
  type t;
  let leq: (t, t) => bool;
};

module PQueue = (Elem: Comparable) => {
  [@deriving sexp]
  type t =
    | Leaf
    | Node(Elem.t, int, t, t);

  let rank =
    fun
    | Leaf => 0
    | Node(_, rank, _, _) => rank;

  let merge_with_root = (root: Elem.t, q1: t, q2: t): t => {
    let (r1, r2) = (rank(q1), rank(q2));
    let (rank, left, right) =
      if (r1 >= r2) {
        (r1, q1, q2);
      } else {
        (r2, q2, q1);
      };
    Node(root, rank + 1, left, right);
  };

  let rec merge = (q1: t, q2: t): t =>
    switch (q1, q2) {
    | (Leaf, q2) => q2
    | (q1, Leaf) => q1
    | (Node(e1, _, q1l, q1r), Node(e2, _, q2l, q2r)) =>
      if (Elem.leq(e1, e2)) {
        merge_with_root(e1, q1l, merge(q2, q1r));
      } else {
        merge_with_root(e2, q2l, merge(q1, q2r));
      }
    };

  let empty = Leaf;

  let push = (e: Elem.t, q: t): t => {
    let eq = Node(e, 1, Leaf, Leaf);
    merge(eq, q);
  };

  let pop = (q: t): option((Elem.t, t)) =>
    switch (q) {
    | Leaf => None
    | Node(e, _, q1, q2) => Some((e, merge(q1, q2)))
    };

  // only used for display
  let rec list_of_t =
    fun
    | Leaf => []
    | Node(e, _, q1, q2) => [e] @ list_of_t(q1) @ list_of_t(q2);
};
