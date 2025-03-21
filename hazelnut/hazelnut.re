open Sexplib.Std;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Product(t, t)
    | Num
    | Bool
    | Unit
    | List
    | Hole;
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t)
    | LProduct(t, Htyp.t)
    | RProduct(Htyp.t, t);
};

module ProdSide = {
  [@deriving (sexp, compare)]
  type t =
    | Fst
    | Snd;
};

module Bind = {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);
};

module MarkMessage = {
  [@deriving (sexp, compare)]
  type t =
    | Free
    | NonArrowAp
    | NonArrowLam
    | NonProdPair
    | NonProdProj
    | LamAnnIncon
    | Inconsistent;
};

module Mark = {
  [@deriving (sexp, compare)]
  type t =
    | Unmarked
    | Marked;
};

let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(t) => t
  | LArrow(zt1, t2) => Arrow(erase_typ(zt1), t2)
  | RArrow(t1, zt2) => Arrow(t1, erase_typ(zt2))
  | LProduct(zt1, t2) => Product(erase_typ(zt1), t2)
  | RProduct(t1, zt2) => Product(t1, erase_typ(zt2))
  };
};

let matched_arrow_typ = (t: Htyp.t): (Htyp.t, Htyp.t, Mark.t) => {
  switch (t) {
  | Arrow(t1, t2) => (t1, t2, Unmarked)
  | Hole => (Hole, Hole, Unmarked)
  | _ => (Hole, Hole, Marked)
  };
};

let matched_arrow_typ_opt =
    (t: option(Htyp.t)): (option(Htyp.t), option(Htyp.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (t_in, t_out, m) = matched_arrow_typ(t);
    (Some(t_in), Some(t_out), m);
  | None => (None, None, Unmarked)
  };
};

let matched_product_typ = (t: Htyp.t): (Htyp.t, Htyp.t, Mark.t) => {
  switch (t) {
  | Product(t1, t2) => (t1, t2, Unmarked)
  | Hole => (Hole, Hole, Unmarked)
  | _ => (Hole, Hole, Marked)
  };
};

let matched_product_typ_opt =
    (t: option(Htyp.t)): (option(Htyp.t), option(Htyp.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (t1, t2, m) = matched_product_typ(t);
    (Some(t1), Some(t2), m);
  | None => (None, None, Unmarked)
  };
};

let matched_proj_typ = (prod_side: ProdSide.t, t: Htyp.t): (Htyp.t, Mark.t) => {
  let (t_fst, t_snd, m) = matched_product_typ(t);
  switch (prod_side) {
  | Fst => (t_fst, m)
  | Snd => (t_snd, m)
  };
};

let matched_proj_typ_opt =
    (prod_side: ProdSide.t, t: option(Htyp.t)): (option(Htyp.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (t, m) = matched_proj_typ(prod_side, t);
    (Some(t), m);
  | None => (None, Unmarked)
  };
};

let rec is_type_consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Hole, _)
  | (_, Hole) => true
  | (Num, Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    is_type_consistent(t11, t21) && is_type_consistent(t12, t22)
  | (Product(t11, t12), Product(t21, t22)) =>
    is_type_consistent(t11, t21) && is_type_consistent(t12, t22)
  | _ => false
  };
};

let type_consistent = (t1: Htyp.t, t2: Htyp.t): Mark.t => {
  is_type_consistent(t1, t2) ? Unmarked : Marked;
};

let type_consistent_opt = (t1: option(Htyp.t), t2: option(Htyp.t)): Mark.t => {
  switch (t1, t2) {
  | (None, _) => Unmarked
  | (_, None) => Unmarked
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

let product_unless =
    (t1: option(Htyp.t), t2: option(Htyp.t), unless: option(Htyp.t))
    : option(Htyp.t) => {
  switch (unless, t1, t2) {
  | (None, None, None)
  | (None, Some(_), None)
  | (None, None, Some(_)) => None
  | (None, Some(t1), Some(t2)) => Some(Product(t1, t2))
  | (Some(_), _, _) => None
  };
};

exception Unimplemented;
exception Unreachable;
