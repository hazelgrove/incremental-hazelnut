// open Sexplib.Std;
open Hazelnut;
open Incremental;
open State;
open Actions;

module Pexp: {
  [@deriving (sexp, compare)]
  type t;
};

let pexp_of_iexp: (Iexp.upper, Istate.t) => Pexp.t;
let pexp_of_root: Istate.t => Pexp.t;
let pexp_of_htyp: Htyp.t => Pexp.t;
let string_of_pexp: Pexp.t => string;
let string_of_action: Iaction.t => string;
