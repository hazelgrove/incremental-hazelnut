// open Typ;
open Id;
open Node;
open Tree;
open UpdateQueue;
// open Sexplib.Std;
// open Sexplib0;

module IdMap = {
  type term = Hashtbl.t(Id.t, Node.t);
  type edge = Hashtbl.t(Id.t, Node.edge);
  // let sexp_of_t = _ => Sexp.Atom("unimplemented");
  // let t_of_sexp = _ => failwith("IdMap of sexp");
};

module BinderSet = {
  type t = Hashtbl.t(string, Tree.t(Node.t));
  // let sexp_of_t = _ => Sexp.Atom("unimplemented");
  // let t_of_sexp = _ => failwith("BinderSet of sexp");
};

module State = {
  // [@deriving sexp]
  type t = {
    cursor: Node.t,
    root: Node.t,
    term_map: IdMap.term,
    edge_map: IdMap.edge,
    queue: UpdateQueue.t,
    counter: Id.counter,
    binders: BinderSet.t,
  };
};

let initial_state = (): State.t => {
  let initial_counter = Id.initial_counter();
  let initial_term = Node.initial(initial_counter);
  let initial_term_map = Hashtbl.create(100);
  let initial_edge_map = Hashtbl.create(100);
  let initial_queue = UpdateQueue.empty();
  let initial_binder = Hashtbl.create(100);
  {
    cursor: initial_term,
    root: initial_term,
    term_map: initial_term_map,
    edge_map: initial_edge_map,
    queue: initial_queue,
    counter: initial_counter,
    binders: initial_binder,
  };
};

let get_parent = (state: State.t, e: Node.t): option(Node.t) => {
  e.root
    ? None
    : {
      let parent_edges = e.parent_edges;
      assert(List.length(parent_edges) == 1);
      let parent_edge = List.hd(parent_edges);
      let parent_id = fst(parent_edge.source);
      Some(Hashtbl.find(state.term_map, parent_id));
    };
};
