// open Sexplib.Std;

module Element: {
  [@deriving sexp]
  type t;
};

module OM: {
  [@deriving sexp]
  type t;

  let init: unit => (Element.t, t);

  let insert: (Element.t, t) => Element.t;
  let insert_before: (Element.t, t) => Element.t;

  let leq: (Element.t, Element.t) => bool;
};
