module Element: {
  type t;
};

module OM: {
  type t;

  let insert: (Element.t, t) => Element.t;

  let leq: (Element.t, Element.t) => bool;
};
