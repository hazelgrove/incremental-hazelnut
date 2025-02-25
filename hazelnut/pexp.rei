// open Sexplib.Std;
open Incremental;
open State;
open Actions;

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
    | Interval(float, t, float)
    | Mark(t, string);
};

let pexp_of_iexp: (Iexp.upper, Istate.t) => Pexp.t;
let pexp_of_root: (Iexp.parent, Istate.t) => Pexp.t;
let string_of_pexp: Pexp.t => string;
let string_of_action: Iaction.t => string;
