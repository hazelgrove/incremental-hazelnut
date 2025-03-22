open Sexplib0;

module type Comparable = {
  [@deriving sexp]
  type t;
  let leq: (t, t) => bool;
};

module PQueue = (Elem: Comparable) => {
  type t = Dynarray.t(Elem.t);
  //let x = Array.create(1)

  let sexp_of_t = _ => Sexp.Atom("unimplemented");
  let t_of_sexp = _ => failwith("PQueue of sexp");

  let empty: unit => t = Dynarray.create;

  let swap = (q: t, i: int, j: int): unit => {
    let tmp = Dynarray.get(q, i);
    Dynarray.set(q, i, Dynarray.get(q, j));
    Dynarray.set(q, j, tmp);
  };

  let has_parent = (i: int): bool => {
    i != 0;
  };

  let parent_idx = (i: int): int => {
    //(i + 1) / 2 - 1
    (i - 1) / 2;
  };

  let _left_child_idx = (i: int): int => {
    //(i + 1) * 2 - 1
    i * 2 + 1;
  };

  let right_child_idx = (i: int): int => {
    //(i + 1) * 2 + 1 - 1
    (i + 1) * 2;
  };

  let has_idx = (q: t, i: int): bool => {
    i < Dynarray.length(q);
  };

  let heap_elm = (q: t, i: int): Elem.t => {
    Dynarray.get(q, i);
  };

  let rec float_to_top = (q: t, i: int): unit =>
    if (has_parent(i)) {
      let p = parent_idx(i);
      if (Elem.leq(heap_elm(q, i), heap_elm(q, p))) {
        swap(q, i, p);
        float_to_top(q, p);
      };
    };

  let rec sink_to_bottom = (q: t, i: int): unit => {
    let rci = right_child_idx(i);
    let lci = rci - 1;
    if (has_idx(q, rci)) {
      let min_ci =
        if (Elem.leq(heap_elm(q, lci), heap_elm(q, rci))) {
          lci;
        } else {
          rci;
        };
      if (Elem.leq(heap_elm(q, min_ci), heap_elm(q, i))) {
        swap(q, i, min_ci);
        sink_to_bottom(q, min_ci);
      };
    } else if (has_idx(q, lci)) {
      if (Elem.leq(heap_elm(q, lci), heap_elm(q, i))) {
        swap(q, i, lci);
        sink_to_bottom(q, lci);
      };
    };
  };

  let push = (elm: Elem.t, q: t): unit => {
    Dynarray.add_last(q, elm);
    float_to_top(q, Dynarray.length(q) - 1);
  };

  let pop = (q: t): option(Elem.t) =>
    if (Dynarray.is_empty(q)) {
      None;
    } else {
      swap(q, 0, Dynarray.length(q) - 1);
      let v = Dynarray.pop_last(q);
      sink_to_bottom(q, 0);
      Some(v);
    };

  let list_of_t = (q: t): list(Elem.t) => Dynarray.to_list(q);
};
