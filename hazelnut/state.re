open Typ;
open Term;
open Tree;
open UpdateQueue;
open Sexplib.Std;
open Sexplib0;
open Order;

module BinderSet = {
  type t = Hashtbl.t(string, Tree.t(Term.t));
  // let sexp_of_t = _ => Sexp.Atom("unimplemented");
  // let t_of_sexp = _ => failwith("BinderSet of sexp");
};

module State = {
  // [@deriving sexp]
  type t = {
    cursor: Term.t,
    root: Term.t,
    queue: UpdateQueue.t,
    binders: BinderSet.t,
  };
};

let initial_state = (): State.t => {
  let initial_term = Term.initial();
  let initial_queue = UpdateQueue.empty();
  let initial_binder = Hashtbl.create(100);
  {
    cursor: initial_term,
    root: initial_term,
    queue: initial_queue,
    binders: initial_binder,
  };
};
