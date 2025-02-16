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

let matched_arrow_typ = (t: Htyp.t): (Htyp.t, Htyp.t, bool) => {
  switch (t) {
  | Arrow(t1, t2) => (t1, t2, false)
  | Hole => (Hole, Hole, false)
  | _ => (Hole, Hole, true)
  };
};

let matched_arrow_typ_opt =
    (t: option(Htyp.t)): (option(Htyp.t), option(Htyp.t), bool) => {
  switch (t) {
  | Some(t) =>
    let (t_in, t_out, m) = matched_arrow_typ(t);
    (Some(t_in), Some(t_out), m);
  | None => (None, None, false)
  };
};

let rec type_consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Hole, _) => true
  | (_, Hole) => true
  | (Num, Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    type_consistent(t11, t21) && type_consistent(t12, t22)
  | _ => false
  };
};

let type_consistent_opt = (t1: option(Htyp.t), t2: option(Htyp.t)): bool => {
  switch (t1, t2) {
  | (None, _) => true
  | (_, None) => true
  | (Some(t1), Some(t2)) => type_consistent(t1, t2)
  };
};

let arrow_unless =
    (t1: Htyp.t, t2: option(Htyp.t), unless: option(Htyp.t))
    : option(Htyp.t) => {
  switch (unless, t2) {
  | (None, None) => None
  | (None, Some(t2)) => Some(Arrow(t1, t2))
  | (Some(_), _) => None
  };
};

exception Unimplemented;
