open Sexplib.Std;
open Hazelnut;
open Incremental;

let compare_string = String.compare;
let compare_int = Int.compare;
let compare_float = Float.compare;

// let show_intervals = false;

let string_of_child: Child.t => string =
  fun
  | One => "One"
  | Two => "Two"
  | Three => "Three";

let string_of_action: Iaction.t => string =
  fun
  | MoveUp => "MoveUp"
  | MoveDown(c) => "MoveDown(" ++ string_of_child(c) ++ ")"
  | Delete => "Delete"
  | WrapArrow(c) => "WrapArrow(" ++ string_of_child(c) ++ ")"
  | InsertNumType => "InsertNumType"
  | InsertNumLit(x) => "InsertNumLit(" ++ string_of_int(x) ++ ")"
  | InsertVar(s) => "InsertVar(\"" ++ s ++ "\")"
  | WrapPlus(c) => "WrapPlus(" ++ string_of_child(c) ++ ")"
  | WrapAp(c) => "WrapAp(" ++ string_of_child(c) ++ ")"
  | WrapLam => "WrapLam"
  | WrapAsc => "WrapAsc"
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
    | Var(string)
    | Lam(t, t, t)
    | Ap(t, t)
    | NumLit(int)
    | Plus(t, t)
    | Asc(t, t)
    | Hole
    | Interval(float, t, float)
    | Mark(t, string);
};

let rec pexp_of_htyp: Hazelnut.Htyp.t => Pexp.t =
  fun
  | Arrow(t1, t2) => Arrow(pexp_of_htyp(t1), pexp_of_htyp(t2))
  | Num => Num
  | Hole => Hole;

let pexp_of_htyp_opt: option(Htyp.t) => Pexp.t =
  fun
  | Some(t) => pexp_of_htyp(t)
  | None => Var("■");

let rec pexp_of_ztyp: Hazelnut.Ztyp.t => Pexp.t =
  fun
  | Cursor(t) => Cursor(pexp_of_htyp(t))
  | LArrow(z, t) => Arrow(pexp_of_ztyp(z), pexp_of_htyp(t))
  | RArrow(t, z) => Arrow(pexp_of_htyp(t), pexp_of_ztyp(z));

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
  | LamAnnIncon => "LamAnnIncon"
  | Inconsistent => "Inconsistent";
};

let pexp_markif = (b: Mark.t, m: MarkMessage.t, exp: Pexp.t): Pexp.t =>
  switch (b) {
  | Unmarked => exp
  | Marked => Mark(exp, string_of_mark_message(m))
  };

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

let rec pexp_of_iexp = (e: Iexp.upper, s: Istate.t): Pexp.t => {
  let middle = pexp_of_iexp_middle(e.middle, s);

  let with_cursor: Pexp.t =
    switch (s.c) {
    | CursorExp(e') when e' === e => Cursor(middle)
    | _ => middle
    };

  // let with_interval: Pexp.t =
  //   show_intervals
  //     ? Interval(fst(e.interval), with_cursor, snd(e.interval))
  //     : with_cursor;

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
    };
  };
  let with_new_types =
    List.fold_left(
      implement_updates,
      with_cursor,
      UpdateQueue.list_of_t(s.q),
    );
  with_new_types;
}

and pexp_of_iexp_middle = (e: Iexp.middle, s: Istate.t): Pexp.t => {
  switch (e) {
  | Var(x, m, _binders) => pexp_markif(m, Free, Var(x))
  | NumLit(x) => NumLit(x)
  | Plus(e1, e2) =>
    Plus(pexp_of_iexp_lower(e1, s), pexp_of_iexp_lower(e2, s))
  | Lam(x, t, m1, m2, body, _bound_vars) =>
    let pb: Pexp.t =
      switch (s.c) {
      | CursorBind(e') when e'.middle === e =>
        Cursor(pexp_of_bind(x.contents))
      | _ => pexp_of_bind(x.contents)
      };
    let pt =
      switch (s.c) {
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
    | NewAna(Lower(e')) when e === e' => Some(e.ana)
    | NewAna(_) => None
    | NewSyn(_) => None
    | NewAnn(_) => None
    | NewAsc(_) => None
    };
  };
  switch (List.filter_map(filter_updates, UpdateQueue.list_of_t(s.q))) {
  | [t, ..._] => NewAna(d, pexp_of_htyp_opt(t))
  | [] => d
  };
};

let pexp_of_root = (parent: Iexp.parent, s: Istate.t): Pexp.t => {
  switch (parent) {
  | Root(e) =>
    let d = pexp_of_iexp(e.root_child, s);
    let filter_updates = (u: Update.t) => {
      switch (u) {
      | NewAna(Root(e')) when e' === e => true
      | NewAna(_) => false
      | NewSyn(_) => false
      | NewAnn(_) => false
      | NewAsc(_) => false
      };
    };
    List.exists(filter_updates, UpdateQueue.list_of_t(s.q))
      ? NewAna(d, pexp_of_htyp_opt(None)) : d;
  | _ => failwith("non-root root (pexp)")
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
  | Var(_) => Atom
  | Lam(_) => Atom
  | Ap(_) => Left
  | NumLit(_) => Atom
  | Plus(_) => Left
  | Asc(_) => Left
  | Hole => Atom
  | Interval(_) => Atom
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
  | Interval(n1, e, n2) =>
    "{"
    ++ string_of_float(n1)
    ++ "]"
    ++ string_of_pexp(e)
    ++ "["
    ++ string_of_float(n2)
    ++ "}"
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
