module Htyp: {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Product(t, t)
    | Num
    | Hole;
};

module Ztyp: {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t)
    | LProduct(t, Htyp.t)
    | RProduct(Htyp.t, t);
};

module Bind: {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);
};

module MarkMessage: {
  [@deriving (sexp, compare)]
  type t =
    | Free
    | NonArrowAp
    | NonArrowLam
    | LamAnnIncon
    | Inconsistent;
};

module Mark: {
  [@deriving (sexp, compare)]
  type t =
    | Unmarked
    | Marked;
};

exception Unimplemented;

let erase_typ: Ztyp.t => Htyp.t;
let matched_arrow_typ: Htyp.t => (Htyp.t, Htyp.t, Mark.t);
let matched_arrow_typ_opt:
  option(Htyp.t) => (option(Htyp.t), option(Htyp.t), Mark.t);
let matched_product_typ: Htyp.t => (Htyp.t, Htyp.t, Mark.t);
let matched_product_typ_opt:
  option(Htyp.t) => (option(Htyp.t), option(Htyp.t), Mark.t)
let type_consistent: (Htyp.t, Htyp.t) => Mark.t;
let type_consistent_opt: (option(Htyp.t), option(Htyp.t)) => Mark.t;
let arrow_unless:
  (Htyp.t, option(Htyp.t), option(Htyp.t)) => option(Htyp.t);
let product_unless: (option(Htyp.t), option(Htyp.t), option(Htyp.t)) => option(Htyp.t);
