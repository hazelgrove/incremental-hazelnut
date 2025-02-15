open Sexplib.Std;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Bind = {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);
};

module Mark = {
  [@deriving (sexp, compare)]
  type t =
    | Free
    | NonArrowAp
    | NonArrowLam
    | LamAscIncon
    | Inconsistent;
};

let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(t) => t
  | LArrow(zt1, t2) => Arrow(erase_typ(zt1), t2)
  | RArrow(t1, zt2) => Arrow(t1, erase_typ(zt2))
  };
};

let _matched_arrow_typ = (t: Htyp.t): option((Htyp.t, Htyp.t)) => {
  switch (t) {
  | Arrow(t1, t2) => Some((t1, t2))
  | Hole => Some((Hole, Hole))
  | _ => None
  };
};

let rec _type_consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Hole, _) => true
  | (_, Hole) => true
  | (Num, Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    _type_consistent(t11, t21) && _type_consistent(t12, t22)
  | _ => false
  };
};

exception Unimplemented;
