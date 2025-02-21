// open Sexplib.Std;
open Incremental;
open Order;

module Pexp: {
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
    | Interval(Element.t, t, Element.t)
    | Mark(t, string);
};

let pexp_of_iexp: (Iexp.upper, Istate.t) => Pexp.t;
let pexp_of_root: (Iexp.parent, Istate.t) => Pexp.t;
let string_of_pexp: Pexp.t => string;
