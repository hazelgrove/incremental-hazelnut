open Sexplib.Std;
open Hazelnut;
open Incremental;

let compare_string = String.compare;
let compare_int = Int.compare;

module Pexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(t)
    | NewSyn(t, t)
    | NewAna(t, t)
    | New(t)
    | Arrow(t, t)
    | Num
    | Var(string)
    | Lam(t, t, t)
    | Ap(t, t)
    | NumLit(int)
    | Plus(t, t)
    | Asc(t, t)
    | Hole
    | Mark(t, string);
};

let rec pexp_of_htyp: Hazelnut.Htyp.t => Pexp.t =
  fun
  | Arrow(t1, t2) => Arrow(pexp_of_htyp(t1), pexp_of_htyp(t2))
  | Num => Num
  | Hole => Hole;

let rec pexp_of_ztyp: Hazelnut.Ztyp.t => Pexp.t =
  fun
  | Cursor(t) => Cursor(pexp_of_htyp(t))
  | LArrow(z, t) => Arrow(pexp_of_ztyp(z), pexp_of_htyp(t))
  | RArrow(t, z) => Arrow(pexp_of_htyp(t), pexp_of_ztyp(z));

let pexp_of_bind: Hazelnut.Bind.t => Pexp.t = {
  fun
  | Hole => Hole
  | Var(x) => Var(x);
};

let string_of_mark_message: Hazelnut.MarkMessage.t => string = {
  fun
  | Free => "Free"
  | NonArrowAp => "NonArrowAp"
  | NonArrowLam => "NonArrowLam"
  | LamAnnIncon => "LamAnnIncon"
  | Inconsistent => "Inconsistent";
};

let pexp_markif = (b: Mark.t, m: MarkMessage.t, exp: Pexp.t): Pexp.t =>
  switch (b) {
  | Unmarked => exp
  | Marked => Mark(exp, string_of_mark_message(m))
  };

let rec pexp_of_iexp = (e: Iexp.upper, s: Istate.t): Pexp.t => {
  let d = pexp_of_iexp_middle(e.middle, s);
  let d: Pexp.t =
    switch (s.c) {
    | CursorExp(e') when e' === e => Cursor(d)
    | CursorBind(e') when e' === e =>
      switch (d) {
      | Lam(x, t, body) => Lam(Cursor(x), t, body)
      | _ => failwith("CursorBind on non-function")
      }
    | _ => d
    };
  let newify: Pexp.t => Pexp.t =
    fun
    // | New(t) => New(t)
    | t => New(t);
  let implement_updates =
      ((d, syn): (Pexp.t, option(Htyp.t)), u: Update.t)
      : (Pexp.t, option(Htyp.t)) => {
    switch (u) {
    | NewSyn(e') when e === e' => (d, e.syn)
    | NewSyn(_) => (d, syn)
    | NewAna(_) => (d, syn)
    | NewAnn(e') when e === e' =>
      switch (d) {
      | Cursor(Lam(x, t, body)) => (Cursor(Lam(x, newify(t), body)), syn)
      | Lam(x, t, body) => (Lam(x, newify(t), body), syn)
      | _ => failwith("NewAnn on non-function")
      }
    | NewAnn(_) => (d, syn)
    | NewAsc(e') when e === e' =>
      switch (d) {
      | Cursor(Asc(body, t)) => (Cursor(Asc(body, newify(t))), syn)
      | Asc(body, t) => (Asc(body, newify(t)), syn)
      | _ => failwith("NewAsc on non-ascription")
      }
    | NewAsc(_) => (d, syn)
    };
  };
  switch (
    List.fold_left(implement_updates, (d, None), UpdateQueue.list_of_t(s.q))
  ) {
  | (d', Some(t)) => NewSyn(d', pexp_of_htyp(t))
  | (d', None) => d'
  };
}

and pexp_of_iexp_middle = (e: Iexp.middle, s: Istate.t): Pexp.t => {
  switch (e) {
  | Var(x, m, _binders) => pexp_markif(m, Free, Var(x))
  | NumLit(x) => NumLit(x)
  | Plus(e1, e2) =>
    Plus(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s))
  | Lam(x, t, m1, m2, body, _bound_vars) =>
    let pt =
      switch (s.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    pexp_markif(
      m2.contents,
      LamAnnIncon,
      pexp_markif(
        m1.contents,
        NonArrowLam,
        Lam(pexp_of_bind(x), pt, pexp_of_iexp_lower(body, s)),
      ),
    );
  | Ap(e1, m, e2) =>
    pexp_markif(
      m.contents,
      NonArrowAp,
      Ap(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s)),
    )
  | Asc(body, t) =>
    let pt =
      switch (s.c) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    Asc(pexp_of_iexp_lower(body, s), pt);
  | EHole => Hole
  };
}

and pexp_of_iexp_lower = (e: Iexp.lower, s: Istate.t): Pexp.t => {
  let d = pexp_markif(e.marked, Inconsistent, pexp_of_iexp(e.child, s));
  let filter_updates = (u: Update.t) => {
    switch (u) {
    | NewAna(e') when e === e' => e.ana
    | NewAna(_) => None
    | NewSyn(_) => None
    | NewAnn(_) => None
    | NewAsc(_) => None
    };
  };
  switch (List.filter_map(filter_updates, UpdateQueue.list_of_t(s.q))) {
  | [t, ..._] => NewAna(d, pexp_of_htyp(t))
  | [] => d
  };
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
  | Var(_) => 0
  | Lam(_) => 0
  | Ap(_) => 2
  | NumLit(_) => 0
  | Plus(_) => 3
  | Asc(_) => 4
  | Hole => 0
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
  | Var(_) => Atom
  | Lam(_) => Atom
  | Ap(_) => Left
  | NumLit(_) => Atom
  | Plus(_) => Left
  | Asc(_) => Left
  | Hole => Atom
  | Mark(_, _) => Atom;

let rec string_of_pexp: Pexp.t => string =
  fun
  | Cursor(e) => "👉" ++ string_of_pexp(e) ++ "👈"
  | NewSyn(e, t) as outer =>
    paren(e, outer, Side.Left) ++ "⇒" ++ paren(t, outer, Side.Right) ++ "*"
  | NewAna(e, t) as outer =>
    paren(e, outer, Side.Left) ++ "⇐" ++ paren(t, outer, Side.Right) ++ "*"
  | New(t) => string_of_pexp(t) ++ "*"
  | Arrow(t1, t2) as outer =>
    paren(t1, outer, Side.Left) ++ " → " ++ paren(t2, outer, Side.Right)
  | Num => "Num"
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
  | NumLit(n) => string_of_int(n)
  | Plus(e1, e2) as outer =>
    paren(e1, outer, Side.Left) ++ " + " ++ paren(e2, outer, Side.Right)
  | Asc(e, t) as outer =>
    paren(e, outer, Side.Left) ++ ": " ++ paren(t, outer, Side.Right)
  | Hole => "?"
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
