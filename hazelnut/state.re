// open Typ;
open Id;
open Node;
open Tree;
open UpdateQueue;
// open Sexplib.Std;
// open Sexplib0;

module IdMap = {
  type node = Hashtbl.t(Id.t, Node.t);
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
    program_root: Node.t,
    node_map: IdMap.node,
    edge_map: IdMap.edge,
    queue: UpdateQueue.t,
    counter: Id.counter,
    binders: BinderSet.t,
  };

  let add_edge = (state: t, edge: Node.edge) => {
    let (source_id, source_position) = edge.source;
    let destination_id = edge.destination;
    Hashtbl.add(state.edge_map, edge.id, edge);
    let source_node = Hashtbl.find(state.node_map, source_id);
    let destination_node = Hashtbl.find(state.node_map, destination_id);
    let add_edge = children => children @ [edge];
    map_children_at_position(source_node, source_position, add_edge);
    destination_node.parent_edges = destination_node.parent_edges @ [edge];
  };
};

let initial_state = (): State.t => {
  let initial_counter = Id.initial_counter();
  let initial_node = Node.initial(initial_counter);
  let initial_node_map = Hashtbl.create(100);
  let initial_edge_map = Hashtbl.create(100);
  let initial_queue = UpdateQueue.empty();
  let initial_binder = Hashtbl.create(100);
  {
    cursor: initial_node,
    program_root: initial_node,
    node_map: initial_node_map,
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
      let parent_edges = Node.live_parent_edges(e);
      assert(List.length(parent_edges) == 1);
      let parent_edge = List.hd(parent_edges);
      let parent_id = fst(parent_edge.source);
      Some(Hashtbl.find(state.node_map, parent_id));
    };
};
