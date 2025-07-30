open Sexplib.Std;

module Bind = {
  [@deriving sexp]
  type t =
    | Hole
    | Var(string);

  let compare = (a, b) => {
    switch (a, b) {
    | (Hole, Hole) => 0
    | (Hole, Var(_)) => (-1)
    | (Var(_), Hole) => 1
    | (Var(a), Var(b)) => String.compare(a, b)
    };
  };
};

module Mark = {
  [@deriving (sexp, compare)]
  type t =
    | Unmarked
    | Marked;
};

module Htyp = {
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

module Ztyp = {
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

module ProdSide = {
  [@deriving (sexp, compare)]
  type t =
    | Fst
    | Snd;
};

module MarkMessage = {
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

let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(t) => t
  | LArrow(zt1, t2) => Arrow(erase_typ(zt1), t2)
  | RArrow(t1, zt2) => Arrow(t1, erase_typ(zt2))
  | LProduct(zt1, t2) => Product(erase_typ(zt1), t2)
  | RProduct(t1, zt2) => Product(t1, erase_typ(zt2))
  | ForAll(name, body_t) => ForAll(name, erase_typ(body_t))
  | ForAllCursorBind(name, body_t) => ForAll(name, body_t)
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

let matched_forall_typ = (t: Htyp.t): (Bind.t, Htyp.t, Mark.t) => {
  switch (t) {
  | ForAll(x, t) => (x, t, Mark.Unmarked)
  | Hole => (Bind.Hole, Htyp.Hole, Mark.Unmarked)
  | _ => (Bind.Hole, Htyp.Hole, Mark.Marked)
  };
};

let matched_forall_typ_opt =
    (t: option(Htyp.t)): (Bind.t, option(Htyp.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (x, t1, m) = matched_forall_typ(t);
    (x, Some(t1), m);
  | None => (Bind.Hole, None, Mark.Unmarked)
  };
};

let matched_forall_typ_of_bind = (t: Htyp.t, x: Bind.t): (Htyp.t, Mark.t) => {
  switch (t) {
  | ForAll(y, t) when x == y => (t, Mark.Unmarked)
  | Hole => (Htyp.Hole, Mark.Unmarked)
  | _ => (Htyp.Hole, Mark.Marked)
  };
};

let matched_forall_typ_of_bind_opt =
    (t: option(Htyp.t), x: Bind.t): (option(Htyp.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (t1, m) = matched_forall_typ_of_bind(t, x);
    (Some(t1), m);
  | None => (None, Mark.Unmarked)
  };
};

module RenamingMap = Map.Make(String);

let rec is_type_consistent =
        (
          ctx_fwd: RenamingMap.t(String.t),
          ctx_back: RenamingMap.t(String.t),
          t1: Htyp.t,
          t2: Htyp.t,
        )
        : bool => {
  switch (t1, t2) {
  | (Hole, _)
  | (_, Hole) => true
  | (Unit, Unit) => true
  | (Bool, Bool) => true
  | (List, List) => true
  | (Num, Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    is_type_consistent(ctx_fwd, ctx_back, t11, t21)
    && is_type_consistent(ctx_fwd, ctx_back, t12, t22)
  | (Product(t11, t12), Product(t21, t22)) =>
    is_type_consistent(ctx_fwd, ctx_back, t11, t21)
    && is_type_consistent(ctx_fwd, ctx_back, t12, t22)
  | (TypVar(Hole, Unmarked), TypVar(_, Unmarked))
  | (TypVar(_, Unmarked), TypVar(Hole, Unmarked)) => true
  | (TypVar(Var(v1), Unmarked), TypVar(Var(v2), Unmarked)) =>
    switch (
      RenamingMap.find_opt(v1, ctx_fwd),
      RenamingMap.find_opt(v2, ctx_back),
    ) {
    | (Some(sub_v1), Some(sub_v2)) => v2 == sub_v1 && v1 == sub_v2
    | _ => false
    }
  | (ForAll(Var(v1), t1), ForAll(Hole, t2)) =>
    let new_ctx_fwd = RenamingMap.remove(v1, ctx_fwd);
    is_type_consistent(new_ctx_fwd, ctx_back, t1, t2);
  | (ForAll(Hole, t1), ForAll(Var(v2), t2)) =>
    let new_ctx_back = RenamingMap.remove(v2, ctx_back);
    is_type_consistent(ctx_fwd, new_ctx_back, t1, t2);
  | (ForAll(Var(v1), t1), ForAll(Var(v2), t2)) =>
    let new_ctx_fwd = RenamingMap.add(v1, v2, ctx_fwd);
    let new_ctx_back = RenamingMap.add(v2, v1, ctx_back);
    is_type_consistent(new_ctx_fwd, new_ctx_back, t1, t2);
  | _ => false
  };
};

let type_consistent = (t1: Htyp.t, t2: Htyp.t): Mark.t => {
  is_type_consistent(RenamingMap.empty, RenamingMap.empty, t1, t2)
    ? Unmarked : Marked;
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

let forall_unless =
    (alpha: Bind.t, body_t: option(Htyp.t), unless: option(Htyp.t))
    : option(Htyp.t) => {
  switch (unless, alpha, body_t) {
  | (Some(_), _, _)
  | (None, _, None) => None
  | (None, alpha, Some(body_t)) => Some(ForAll(alpha, body_t))
  };
};

// Sub
let rec substitute = (arg: Htyp.t, bind: Bind.t, target: Htyp.t): Htyp.t => {
  switch (bind) {
  | Hole => target
  | Var(x) =>
    switch (target) {
    | TypVar(name, _) =>
      switch (name) {
      | Var(y) when x == y => arg
      | _ => target
      }
    | ForAll(forall_bind, body) =>
      switch (forall_bind) {
      | Var(y) when x == y => target // Shadowing
      | _ => ForAll(forall_bind, substitute(arg, bind, body))
      }
    | Arrow(input, output) =>
      Arrow(substitute(arg, bind, input), substitute(arg, bind, output))
    | Product(first, second) =>
      Product(substitute(arg, bind, first), substitute(arg, bind, second))
    | _ => target
    }
  };
};

// DSub
let substitute_opt =
    (arg: Htyp.t, bind: Bind.t, target: option(Htyp.t)): option(Htyp.t) => {
  switch (target) {
  | None => None
  | Some(target) => Some(substitute(arg, bind, target))
  };
};

exception Unimplemented;
exception Unreachable;
