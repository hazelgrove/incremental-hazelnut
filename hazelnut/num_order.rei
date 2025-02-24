// open Sexplib.Std;

// could be used for debugging?

module Element: {
  [@deriving (sexp, compare)]
  type t;
  let string_of_element: t => string;
};

module OM: {
  [@deriving sexp]
  type t;

  let init: unit => (Element.t, t);

  let insert: (Element.t, t) => Element.t;
  let insert_before: (Element.t, t) => Element.t;

  let leq: (Element.t, Element.t) => bool;
};
