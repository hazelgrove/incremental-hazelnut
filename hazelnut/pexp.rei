// open Sexplib.Std;
open Incremental;

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
    | Lam(string, t, t)
    | Ap(t, t)
    | NumLit(int)
    | Plus(t, t)
    | Asc(t, t)
    | EHole
    | Mark(t, string);
};

let pexp_of_iexp: (Iexp.upper, Istate.t) => Pexp.t;
