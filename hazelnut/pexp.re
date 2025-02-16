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

let string_of_mark: Hazelnut.Mark.t => string = {
  fun
  | Free => "Free"
  | NonArrowAp => "NonArrowAp"
  | NonArrowLam => "NonArrowLam"
  | LamAscIncon => "LamAscIncon"
  | Inconsistent => "Inconsistent";
};

let pexp_markif = (b: bool, m: Mark.t, exp: Pexp.t): Pexp.t =>
  if (b) {
    Mark(exp, string_of_mark(m));
  } else {
    exp;
  };

let rec pexp_of_iexp = (e: Iexp.upper, (cursor, updates): Istate.t): Pexp.t => {
  let d = pexp_of_iexp_middle(e.middle, (cursor, updates));
  let d: Pexp.t =
    switch (cursor) {
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
  switch (List.fold_left(implement_updates, (d, None), updates)) {
  | (d', Some(t)) => NewSyn(d', pexp_of_htyp(t))
  | (d', None) => d'
  };
}

and pexp_of_iexp_middle =
    (e: Iexp.middle, (cursor, updates): Istate.t): Pexp.t => {
  switch (e) {
  | Var(x, m, _binders) => pexp_markif(m, Free, Var(x))
  | NumLit(x) => NumLit(x)
  | Plus(e1, e2) =>
    Plus(
      pexp_of_iexp_lower(e1, (cursor, updates)),
      pexp_of_iexp_lower(e2, (cursor, updates)),
    )
  | Lam(x, t, m1, m2, body, _bound_vars) =>
    let pt =
      switch (cursor) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    pexp_markif(
      m2,
      LamAscIncon,
      pexp_markif(
        m1,
        NonArrowLam,
        Lam(
          pexp_of_bind(x),
          pt,
          pexp_of_iexp_lower(body, (cursor, updates)),
        ),
      ),
    );
  | Ap(e1, m, e2) =>
    pexp_markif(
      m,
      NonArrowAp,
      Ap(
        pexp_of_iexp_lower(e1, (cursor, updates)),
        pexp_of_iexp_lower(e2, (cursor, updates)),
      ),
    )
  | Asc(body, t) =>
    let pt =
      switch (cursor) {
      | CursorTyp(e', zt) when e'.middle === e => pexp_of_ztyp(zt)
      | _ => pexp_of_htyp(t.contents)
      };
    Asc(pexp_of_iexp_lower(body, (cursor, updates)), pt);
  | EHole => Hole
  };
}

and pexp_of_iexp_lower = (e: Iexp.lower, (cursor, updates): Istate.t): Pexp.t => {
  let d =
    pexp_markif(
      e.marked,
      Inconsistent,
      pexp_of_iexp(e.child, (cursor, updates)),
    );
  let filter_updates = (u: Update.t) => {
    switch (u) {
    | NewAna(e') when e === e' => e.ana
    | NewAna(_) => None
    | NewSyn(_) => None
    | NewAnn(_) => None
    | NewAsc(_) => None
    };
  };
  switch (List.filter_map(filter_updates, updates)) {
  | [t, ..._] => NewAna(d, pexp_of_htyp(t))
  | [] => d
  };
};

let _print_iexp_upper: Iexp.upper => unit =
  upper =>
    print_endline(
      "iexp print: " ++ string_of_sexp(Iexp.sexp_of_upper(upper)),
    );
