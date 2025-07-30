open Sexplib.Std;
open Hazelnut;
open Incremental;
open Actions;
open UpdateQueue;
open State;
open Order;

let compare_string = String.compare;
let compare_int = Int.compare;
// let compare_float = Float.compare;

let show_intervals = false;

let string_of_child: Child.t => string =
  fun
  | One => "One"
  | Two => "Two"
  | Three => "Three";

let string_of_prod_side: ProdSide.t => string =
  fun
  | Fst => "fst"
  | Snd => "snd";

let string_of_action: Iaction.t => string =
  fun
  | MoveUp => "MoveUp"
  | MoveDown(c) => "MoveDown(" ++ string_of_child(c) ++ ")"
  | Delete => "Delete"
  | WrapArrow(c) => "WrapArrow(" ++ string_of_child(c) ++ ")"
  | InsertNumType => "InsertNumType"
  | InsertBoolType => "InsertBoolType"
  | InsertUnitType => "InsertUnitType"
  | InsertList => "InserList"
  | InsertNil => "InsertNil"
  | InsertCons => "InsertCons"
  | InsertListRec => "InsertListRec"
  | InsertListMatch => "InsertListMatch"
  | InsertY => "InsertY"
  | InsertLt => "InsertLt"
  | InsertITE => "InsertITE"
  | InsertNumLit(x) => "InsertNumLit(" ++ string_of_int(x) ++ ")"
  | InsertVar(s) => "InsertVar(\"" ++ s ++ "\")"
  | WrapPlus(c) => "WrapPlus(" ++ string_of_child(c) ++ ")"
  | WrapAp(c) => "WrapAp(" ++ string_of_child(c) ++ ")"
  | WrapPair(c) => "WrapPair(" ++ string_of_child(c) ++ ")"
  | WrapProduct(c) => "WrapProduct(" ++ string_of_child(c) ++ ")"
  | WrapProj(prod_side) =>
    "WrapProj(" ++ string_of_prod_side(prod_side) ++ ")"
  | WrapLam => "WrapLam"
  | WrapAsc => "WrapAsc"
  | WrapTypAp => "WrapTypAp"
  | WrapTypFun => "WrapTypFun"
  | WrapForAll => "WrapForAll"
  | InsertTypVar(x) => "InsertTypVar(\"" ++ x ++ "\")"
  | Unwrap(c) => "Unwrap(" ++ string_of_child(c) ++ ")";

module Pexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(t)
    | NewSyn(t, t)
    | NewAna(t, t)
    | New(t)
    | Arrow(t, t)
    | Num
    | Bool
    | Unit
    | List
    | Var(string)
    | Lam(t, t, t)
    | Ap(t, t)
    | NumLit(int)
    | Plus(t, t)
    | Pair(t, t)
    | Product(t, t)
    | Fst(t)
    | Snd(t)
    | Nil
    | Cons
    | Lt
    | ITE(t)
    | ListRec(t)
    | Y(t)
    | Asc(t, t)
    | TypFun(t, t)
    | TypAp(t, t)
    | ForAll(t, t)
    | Hole
    | Interval(string, t, string)
    | Mark(t, string);
};

let pexp_of_bind: Bind.t => Pexp.t = {
  fun
  | Hole => Hole
  | Var(x) => Var(x);
};

let string_of_mark_message: Hazelnut.MarkMessage.t => string = {
  fun
  | Free => "Free"
  | NonArrowAp => "NonArrowAp"
  | NonArrowLam => "NonArrowLam"
  | NonForAllTypAp => "NonForAllTypAp"
  | NonForAllTypFun => "NonForAllTypFun"
  | NonProdPair => "NonProdPair"
  | NonProdProj => "NonProdProj"
  | LamAnnIncon => "LamAnnIncon"
  | Inconsistent => "Inconsistent";
};

let pexp_markif = (b: Mark.t, m: MarkMessage.t, exp: Pexp.t): Pexp.t =>
  switch (b) {
  | Unmarked => exp
  | Marked => Mark(exp, string_of_mark_message(m))
  };

let rec pexp_of_htyp: Hazelnut.Htyp.t => Pexp.t =
  fun
  | ForAll(x, t) => ForAll(pexp_of_bind(x), pexp_of_htyp(t))
  | TypVar(x, m) => pexp_markif(m, MarkMessage.Free, pexp_of_bind(x))
  | Arrow(t1, t2) => Arrow(pexp_of_htyp(t1), pexp_of_htyp(t2))
  | Product(t1, t2) => Product(pexp_of_htyp(t1), pexp_of_htyp(t2))
  | Num => Num
  | Bool => Bool
  | Unit => Unit
  | List => List
  | Hole => Hole;

let pexp_of_htyp_opt: option(Htyp.t) => Pexp.t =
  fun
  | Some(t) => pexp_of_htyp(t)
  | None => Var("■");

let rec pexp_of_ztyp: Hazelnut.Ztyp.t => Pexp.t =
  fun
  | Cursor(t) => Cursor(pexp_of_htyp(t))
  | LArrow(z, t) => Arrow(pexp_of_ztyp(z), pexp_of_htyp(t))
  | RArrow(t, z) => Arrow(pexp_of_htyp(t), pexp_of_ztyp(z))
  | LProduct(z, t) => Product(pexp_of_ztyp(z), pexp_of_htyp(t))
  | RProduct(t, z) => Product(pexp_of_htyp(t), pexp_of_ztyp(z))
  | ForAll(x, t) => ForAll(pexp_of_bind(x), pexp_of_ztyp(t))
  | ForAllCursorBind(x, t) =>
    ForAll(Cursor(pexp_of_bind(x)), pexp_of_htyp(t));

let rec unwrap_extras: Pexp.t => (Pexp.t, Pexp.t => Pexp.t) =
  fun
  | Mark(e, m) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => Mark(rewrap(x), m)));
    }
  | Cursor(e) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => Cursor(rewrap(x))));
    }
  | NewAna(e, t) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => NewAna(rewrap(x), t)));
    }
  | NewSyn(e, t) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => NewSyn(rewrap(x), t)));
    }
  | New(e) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => New(rewrap(x))));
    }
  | Interval(n1, e, n2) => {
      let (e', rewrap) = unwrap_extras(e);
      (e', (x => Interval(n1, rewrap(x), n2)));
    }
  | e => (e, (x => x));

// let string_of_interval = (i: (Order.t, Order.t)) =>
//   "("
//   ++ string_of_sexp(Order.sexp_of_t(fst(i)))
//   ++ " , "
//   ++ string_of_sexp(Order.sexp_of_t(snd(i)))
//   ++ ")";

let rec pexp_of_iexp = (e: Iexp.upper, s: Istate.t): Pexp.t => {
  let middle = pexp_of_iexp_middle(e.middle, s);

  let with_cursor: Pexp.t =
    switch (s.persistent.c) {
    | CursorExp(e') when e' === e => Cursor(middle)
    | _ => middle
    };

  let with_interval: Pexp.t =
    show_intervals
      ? Interval(
          string_of_sexp(Order.sexp_of_t(fst(e.interval))),
          with_cursor,
          string_of_sexp(Order.sexp_of_t(snd(e.interval))),
        )
      : with_cursor;

  let implement_updates = (d: Pexp.t, u: Update.t): Pexp.t => {
    switch (u) {
    | NewSyn(e') when e === e' => NewSyn(d, pexp_of_htyp_opt(e.syn))
    | NewSyn(_) => d
    | NewAna(_) => d
    | NewAnn(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (Lam(x, t, body), rewrap) => rewrap(Lam(x, New(t), body))
      | _ => failwith("NewAnn on non lambda (pexp)")
      }
    | NewAnn(_) => d
    | NewAsc(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (Asc(body, t), rewrap) => rewrap(Asc(body, New(t)))
      | _ => failwith("NewAsc on non ascription (pexp)")
      }
    | NewAsc(_) => d
    | NewListRec(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (ListRec(t), rewrap) => rewrap(ListRec(New(t)))
      | _ => failwith("NewListRec on non ListRec (pexp)")
      }
    | NewListRec(_) => d
    | NewY(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (Y(t), rewrap) => rewrap(Y(New(t)))
      | _ => failwith("NewY on non Y (pexp)")
      }
    | NewY(_) => d
    | NewITE(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (ITE(t), rewrap) => rewrap(ITE(New(t)))
      | _ => failwith("NewITE on non ITE (pexp)")
      }
    | NewITE(_) => d
    | NewTypAp(e') when e === e' =>
      switch (unwrap_extras(d)) {
      | (TypAp(e_fun, t_arg), rewrap) => rewrap(TypAp(e_fun, New(t_arg)))
      | _ => failwith("NewTypAp on non TypAP (pexp)")
      }
    | NewTypAp(_) => d
    };
  };
  let with_new_types =
    List.fold_left(
      implement_updates,
      with_interval,
      UpdateQueue.list_of_t(s.ephemeral.q),
    );
  with_new_types;
}

and pexp_of_iexp_middle = (e: Iexp.middle, s: Istate.t): Pexp.t => {
  switch (e) {
  | EHole => Hole
  | Var(x, m, _binders) => pexp_markif(m.contents, Free, Var(x))
  | NumLit(x) => NumLit(x)
  | Plus(e1, e2) =>
    Plus(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s))
  | Lam(x, t, m1, m2, body, _bound_vars, _typ_binders) =>
    let pb: Pexp.t =
      switch (s.persistent.c) {
      | CursorBind(e') when e'.middle === e =>
        Cursor(pexp_of_bind(x.contents))
      | _ => pexp_of_bind(x.contents)
      };
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    let lower = pexp_of_iexp_lower(body, s);
    pexp_markif(
      m2.contents,
      LamAnnIncon,
      pexp_markif(m1.contents, NonArrowLam, Lam(pb, pt, lower)),
    );
  | Ap(e1, m, e2) =>
    pexp_markif(
      m.contents,
      NonArrowAp,
      Ap(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s)),
    )
  | Pair(e1, e2, m) =>
    pexp_markif(
      m.contents,
      NonProdPair,
      Pair(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s)),
    )
  | Proj(proj_side, e, m) =>
    pexp_markif(
      m.contents,
      NonProdProj,
      switch (proj_side) {
      | Fst => Fst(pexp_of_iexp_lower(e, s))
      | Snd => Snd(pexp_of_iexp_lower(e, s))
      },
    )
  | Asc(body, t, _typ_binders) =>
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    Asc(pexp_of_iexp_lower(body, s), pt);
  | Nil => Nil
  | Cons => Cons
  | ListRec(t, _typ_binders) =>
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    ListRec(pt);
  | Y(t, _typ_binders) =>
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    Y(pt);
  | ITE(t, _typ_binders) =>
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    ITE(pt);
  | TypFun(x, m, e_body, _typ_binders) =>
    let pb: Pexp.t =
      switch (s.persistent.c) {
      | CursorBind(e') when e'.middle === e =>
        Cursor(pexp_of_bind(x.contents))
      | _ => pexp_of_bind(x.contents)
      };
    let body_lower = pexp_of_iexp_lower(e_body, s);
    pexp_markif(m.contents, NonForAllTypFun, TypFun(pb, body_lower));
  | TypAp(e_fun, m, t_arg, _typ_binders) =>
    let pt =
      switch (s.persistent.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t_arg.contents)
      };
    let fun_lower = pexp_of_iexp_lower(e_fun, s);
    pexp_markif(m.contents, NonForAllTypAp, TypAp(fun_lower, pt));
  };
}

and pexp_of_iexp_lower = (e: Iexp.lower, s: Istate.t): Pexp.t => {
  let d = pexp_markif(e.marked, Inconsistent, pexp_of_iexp(e.child, s));
  let filter_updates = (u: Update.t) => {
    switch (u) {
    | NewAna(Lower(e')) when e === e' => Some(e.ana)
    | NewAna(_) => None
    | NewSyn(_) => None
    | NewAnn(_) => None
    | NewAsc(_) => None
    | NewListRec(_) => None
    | NewY(_) => None
    | NewITE(_) => None
    | NewTypAp(_) => None
    };
  };
  switch (
    List.filter_map(filter_updates, UpdateQueue.list_of_t(s.ephemeral.q))
  ) {
  | [t, ..._] => NewAna(d, pexp_of_htyp_opt(t))
  | [] => d
  };
};

let pexp_of_root = (s: Istate.t): Pexp.t => {
  let root = s.ephemeral.root;
  let d = pexp_of_iexp(root.root_child, s);
  let filter_updates = (u: Update.t) => {
    switch (u) {
    | NewAna(Root(e')) when e' === root => true
    | NewAna(_) => false
    | NewSyn(_) => false
    | NewAnn(_) => false
    | NewAsc(_) => false
    | NewListRec(_) => false
    | NewY(_) => false
    | NewITE(_) => false
    | NewTypAp(_) => false
    };
  };
  List.exists(filter_updates, UpdateQueue.list_of_t(s.ephemeral.q))
    ? NewAna(d, pexp_of_htyp_opt(None)) : d;
};

// Lower is tighter
let rec prec: Pexp.t => int =
  fun
  | Cursor(e) => prec(e)
  | NewSyn(_, _) => 5
  | NewAna(_, _) => 5
  | New(_) => 3
  | Arrow(_) => 1
  | Num => 0
  | Bool => 0
  | Unit => 0
  | List => 0
  | Var(_) => 0
  | Lam(_) => 0
  | Ap(_) => 2
  | NumLit(_) => 0
  | Plus(_) => 3
  | Pair(_) => 3
  | Fst(_) => 4
  | Snd(_) => 4
  | Product(_) => 3
  | Asc(_) => 4
  | Nil => 0
  | Cons => 0
  | Lt => 0
  | ITE(_) => 4
  | ListRec(_) => 4
  | Y(_) => 4
  | TypFun(_) => 0
  | TypAp(_) => 2
  | ForAll(_) => 1
  | Hole => 0
  | Interval(_) => 0
  | Mark(_, _) => 0;

module Side = {
  type t =
    | Left
    | Right
    | Atom;
};

let rec assoc: Pexp.t => Side.t =
  fun
  | Cursor(e) => assoc(e)
  | NewSyn(_, _) => Left
  | NewAna(_, _) => Left
  | New(_) => Left
  | Arrow(_) => Right
  | Num => Atom
  | Bool => Atom
  | Unit => Atom
  | List => Atom
  | Var(_) => Atom
  | Lam(_) => Atom
  | Ap(_) => Left
  | NumLit(_) => Atom
  | Plus(_) => Left
  | Pair(_) => Left
  | Fst(_) => Left
  | Snd(_) => Left
  | Product(_) => Left
  | Asc(_) => Left
  | Nil
  | Cons => Atom
  | Lt => Atom
  | ITE(_) => Left
  | ListRec(_) => Left
  | Y(_) => Left
  | TypFun(_) => Atom
  | TypAp(_) => Left
  | ForAll(_) => Atom
  | Hole => Atom
  | Interval(_) => Atom
  | Mark(_, _) => Atom;

let rec string_of_pexp: Pexp.t => string =
  fun
  | Cursor(e) => "👉" ++ string_of_pexp(e) ++ "👈"
  | NewSyn(e, t) as outer =>
    paren(e, outer, Side.Left) ++ "⇒" ++ paren(t, outer, Side.Right) ++ "*"
  | NewAna(e, t) as outer =>
    paren(t, outer, Side.Right) ++ "*" ++ "⇒" ++ paren(e, outer, Side.Left)
  | New(t) => string_of_pexp(t) ++ "*"
  | Arrow(t1, t2) as outer =>
    paren(t1, outer, Side.Left) ++ " → " ++ paren(t2, outer, Side.Right)
  | Num => "Num"
  | Bool => "Bool"
  | Unit => "Unit"
  | List => "List"
  | Var(x) => x
  | Lam(x, a, e) =>
    "fun "
    ++ string_of_pexp(x)
    ++ ": "
    ++ string_of_pexp(a)
    ++ " ↦ ("
    ++ string_of_pexp(e)
    ++ ")"

  | Ap(e1, e2) as outer =>
    paren(e1, outer, Side.Left) ++ " " ++ paren(e2, outer, Side.Right)
  | Pair(e1, e2) =>
    "(" ++ string_of_pexp(e1) ++ ", " ++ string_of_pexp(e2) ++ ")"
  | Product(t1, t2) as outer =>
    paren(t1, outer, Side.Left) ++ " × " ++ paren(t2, outer, Side.Right)
  | Fst(e) => string_of_pexp(e) ++ ".fst"
  | Snd(e) => string_of_pexp(e) ++ ".snd"
  | NumLit(n) => string_of_int(n)
  | Plus(e1, e2) as outer =>
    paren(e1, outer, Side.Left) ++ " + " ++ paren(e2, outer, Side.Right)
  | Asc(e, t) as outer =>
    paren(e, outer, Side.Left) ++ ": " ++ paren(t, outer, Side.Right)
  | Hole => "?"
  | Nil => "[]"
  | Cons => "_::_"
  | Lt => "<"
  | ITE(t) => "ITE[" ++ string_of_pexp(t) ++ "]"
  | ListRec(t) => "ListRec[" ++ string_of_pexp(t) ++ "]"
  | Y(t) => "Y[" ++ string_of_pexp(t) ++ "]"
  | TypFun(x, e) =>
    "typfun " ++ string_of_pexp(x) ++ " ↦ (" ++ string_of_pexp(e) ++ ")"
  | TypAp(e, t) as outer =>
    paren(e, outer, Side.Left) ++ " " ++ paren(t, outer, Side.Right)
  | ForAll(x, t) =>
    "forall " ++ string_of_pexp(x) ++ " ↦ (" ++ string_of_pexp(t) ++ ")"
  | Interval(n1, e, n2) =>
    "{" ++ n1 ++ "]" ++ string_of_pexp(e) ++ "[" ++ n2 ++ "}"
  | Mark(e, m) => "{" ++ string_of_pexp(e) ++ " | " ++ m ++ "}"

and paren = (inner: Pexp.t, outer: Pexp.t, side: Side.t): string => {
  let unparenned = string_of_pexp(inner);
  let parenned = "(" ++ unparenned ++ ")";

  let prec_inner = prec(inner);
  let prec_outer = prec(outer);

  if (prec_inner < prec_outer) {
    unparenned;
  } else if (prec_inner > prec_outer) {
    parenned;
  } else {
    switch (assoc(inner), side) {
    | (Side.Left, Side.Right)
    | (Side.Right, Side.Left) => parenned
    | _ => unparenned
    };
  };
};

let _print_iexp_upper: Iexp.upper => unit =
  upper =>
    print_endline(
      "iexp print: " ++ string_of_sexp(Iexp.sexp_of_upper(upper)),
    );
