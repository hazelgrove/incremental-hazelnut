// open Typ;
open Id;
open Term;
open Tree;
open UpdateQueue;
// open Sexplib.Std;
// open Sexplib0;

module IdMap = {
  type t = Hashtbl.t(Id.t, Term.t);
  // let sexp_of_t = _ => Sexp.Atom("unimplemented");
  // let t_of_sexp = _ => failwith("IdMap of sexp");
};

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
    id_map: IdMap.t,
    queue: UpdateQueue.t,
    counter: Id.counter,
    binders: BinderSet.t,
  };
};

let initial_state = (): State.t => {
  let initial_counter = Id.initial_counter();
  let initial_term = Term.initial(initial_counter);
  let initial_id_map = Hashtbl.create(100);
  let initial_queue = UpdateQueue.empty();
  let initial_binder = Hashtbl.create(100);
  {
    cursor: initial_term,
    root: initial_term,
    id_map: initial_id_map,
    queue: initial_queue,
    counter: initial_counter,
    binders: initial_binder,
  };
};
