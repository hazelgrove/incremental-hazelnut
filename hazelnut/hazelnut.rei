module Bind: {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);

  let compare: (t, t) => int;
};

module Mark: {
  [@deriving (sexp, compare)]
  type t =
    | Unmarked
    | Marked;
};

module Htyp: {
  [@deriving (sexp, compare)]
  type t =
    | TypVar(Bind.t, Mark.t)
    | ForAll(Bind.t, t)
    | Arrow(t, t)
    | Product(t, t)
    | Num
    | Bool
    | Unit
    | List
    | Hole;
};

module Ztyp: {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t)
    | LProduct(t, Htyp.t)
    | RProduct(Htyp.t, t)
    | ForAll(Bind.t, t)
    // A second variant of the ForAll which represents cursor selection
    | ForAllCursorBind(Bind.t, Htyp.t);
};

module ProdSide: {
  [@deriving (sexp, compare)]
  type t =
    | Fst
    | Snd;
};

module MarkMessage: {
  [@deriving (sexp, compare)]
  type t =
    | Free
    | NonArrowAp
    | NonArrowLam
    | NonForAllTypAp
    | NonForAllTypFun
    | NonProdPair
    | NonProdProj
    | LamAnnIncon
    | Inconsistent;
};

exception Unimplemented;
exception Unreachable;

let erase_typ: Ztyp.t => Htyp.t;
let matched_arrow_typ: Htyp.t => (Htyp.t, Htyp.t, Mark.t);
let matched_arrow_typ_opt:
  option(Htyp.t) => (option(Htyp.t), option(Htyp.t), Mark.t);
let matched_product_typ: Htyp.t => (Htyp.t, Htyp.t, Mark.t);
let matched_product_typ_opt:
  option(Htyp.t) => (option(Htyp.t), option(Htyp.t), Mark.t);
let matched_proj_typ: (ProdSide.t, Htyp.t) => (Htyp.t, Mark.t);
let matched_proj_typ_opt:
  (ProdSide.t, option(Htyp.t)) => (option(Htyp.t), Mark.t);
let type_consistent: (Htyp.t, Htyp.t) => Mark.t;
let type_consistent_opt: (option(Htyp.t), option(Htyp.t)) => Mark.t;
let matched_forall_typ: Htyp.t => (Bind.t, Htyp.t, Mark.t);
let matched_forall_typ_opt:
  option(Htyp.t) => (Bind.t, option(Htyp.t), Mark.t);
let matched_forall_typ_of_bind: (Htyp.t, Bind.t) => (Htyp.t, Mark.t);
let matched_forall_typ_of_bind_opt:
  (option(Htyp.t), Bind.t) => (option(Htyp.t), Mark.t);
let arrow_unless:
  (Htyp.t, option(Htyp.t), option(Htyp.t)) => option(Htyp.t);
let product_unless:
  (option(Htyp.t), option(Htyp.t), option(Htyp.t)) => option(Htyp.t);
let forall_unless:
  (Bind.t, option(Htyp.t), option(Htyp.t)) => option(Htyp.t);
let substitute: (Htyp.t, Bind.t, Htyp.t) => Htyp.t;
let substitute_opt: (Htyp.t, Bind.t, option(Htyp.t)) => option(Htyp.t);
