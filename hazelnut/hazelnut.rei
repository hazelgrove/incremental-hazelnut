module Htyp: {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Ztyp: {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Bind: {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);
};

module Mark: {
  [@deriving (sexp, compare)]
  type t =
    | Free
    | NonArrowAp
    | NonArrowLam
    | LamAscIncon
    | Inconsistent;
};

exception Unimplemented;

let erase_typ: Ztyp.t => Htyp.t;
let matched_arrow_typ: Htyp.t => (Htyp.t, Htyp.t, bool);
let matched_arrow_typ_opt:
  option(Htyp.t) => (option(Htyp.t), option(Htyp.t), bool);
let type_consistent: (Htyp.t, Htyp.t) => bool;
let type_consistent_opt: (option(Htyp.t), option(Htyp.t)) => bool;
