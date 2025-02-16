// open Sexplib.Std;

module Element: {
  [@implementing sexp]
  type t;
  let t_of_sexp: Sexplib0.Sexp.t => t;
  let sexp_of_t: t => Sexplib0.Sexp.t;
};

module OM: {
  [@implementing sexp]
  type t;
  let t_of_sexp: Sexplib0.Sexp.t => t;
  let sexp_of_t: t => Sexplib0.Sexp.t;

  let init: unit => (Element.t, t);

  let insert: (Element.t, t) => Element.t;
  let insert_before: (Element.t, t) => Element.t;

  let leq: (Element.t, Element.t) => bool;
};
