module Element = {
  type t = float;
};

module OM = {
  type t = ref(list(Element.t));

  let insert = (elem: Element.t, om: t): Element.t => {
    let l = om.contents;
    let prefix = List.filter(e => e <= elem, l);
    let suffix = List.filter(e => e > elem, l);
    let new_elem =
      switch (suffix) {
      | [] => elem +. 1.
      | [h, ..._] => (elem +. h) /. 2.
      };
    om.contents = prefix @ [new_elem] @ suffix;
    new_elem;
  };

  let leq = (e1: Element.t, e2: Element.t) => e1 <= e2;
};
