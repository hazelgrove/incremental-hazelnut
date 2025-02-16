open Sexplib.Std;

module Element = {
  [@deriving sexp]
  type t = float;
};

module OM = {
  [@deriving sexp]
  type t = ref(list(Element.t));

  let init = () => (0., ref([0.]));

  let insert = (elem: Element.t, om: t): Element.t => {
    let l = om.contents;
    let prefix = List.filter(e => e <= elem, l);
    let suffix = List.filter(e => e > elem, l);
    let elem' =
      switch (suffix) {
      | [] => elem +. 2048.
      | [h, ..._] => (elem +. h) /. 2.
      };
    om.contents = prefix @ [elem'] @ suffix;
    elem';
  };

  let insert_before = (elem: Element.t, om: t): Element.t => {
    om.contents = List.map(x => (-1.) *. x, List.rev(om.contents));
    let elem' = insert(elem, om);
    om.contents = List.map(x => (-1.) *. x, List.rev(om.contents));
    elem';
  };

  let leq = (e1: Element.t, e2: Element.t) => e1 <= e2;
};
