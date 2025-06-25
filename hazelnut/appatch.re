open Patch;
open Node;
open State;

let rec root_of_node = (state: State.t, e: Node.t) => {
  switch (get_parent(state, e)) {
  | None => e
  | Some(parent) => root_of_node(state, parent)
  };
};

let edge_of_patch = (patch: Patch.t): Node.edge => {
  let ((source_id, _source_con), source_position) = patch.source;
  let (destination_id, _destination_con) = patch.destination;
  let edge: Node.edge = {
    id: patch.id,
    source: (source_id, source_position),
    destination: destination_id,
    sign: patch.sign,
    meta: patch.meta,
  };
  edge;
};

let con_of_patch = (c: Patch.content): Node.content => {
  switch (c) {
  | Pat(Var(x)) => Pat(Var(x))
  | Typ(Arrow) => Typ(Node.default_typ_data(), Arrow)
  | Exp(Var(x)) => Exp(Node.default_exp_data(), Var(None, x))
  | Exp(Fun(x)) => Exp(Node.default_exp_data(), Fun(None, x))
  | Exp(Ap) => Exp(Node.default_exp_data(), Ap)
  };
};

let create_if_new = (state: State.t, node: Patch.node): Node.t => {
  let (id, con) = node;
  switch (Hashtbl.find_opt(state.node_map, id)) {
  | Some(n) => n
  | None =>
    let n = Node.create_node(id, con_of_patch(con));
    Hashtbl.add(state.node_map, id, n);
    n;
  };
};

let roll = (state: State.t, node: Node.t): unit => {
  let rec loop = (state: State.t, current_node: Node.t, min_id_node: Node.t) =>
    if (current_node.id != node.id) {
      current_node.part_of_unicycle = true;
      let new_node = Option.get(get_parent(state, current_node));
      let new_min = new_node.id < min_id_node.id ? new_node : min_id_node;
      loop(state, new_node, new_min);
    } else {
      min_id_node.root = true;
    };
  loop(state, node, node);
};

let unroll = (state: State.t, node: Node.t): unit => {
  let rec loop = (state: State.t, current_node: Node.t) =>
    if (current_node.id != node.id) {
      current_node.root = false;
      current_node.part_of_unicycle = false;
      let new_node = Option.get(get_parent(state, current_node));
      loop(state, new_node);
    };
  loop(state, node);
};

let appatch = (state: State.t, patch: Patch.t): unit => {
  let ((source_id, source_con), _source_position) = patch.source;
  let (destination_id, destination_con) = patch.destination;
  switch (Hashtbl.find_opt(state.edge_map, patch.id)) {
  // edge ids are unique, so if this id is in the database, the patch must have already been applied.
  | Some(_) => ()
  | None =>
    // if the patch is new, make an edge and add it to the database.
    let edge = edge_of_patch(patch);
    // if the nodes haven't been seen before, make them
    let source_node = create_if_new(state, (source_id, source_con));
    let destination_node =
      create_if_new(state, (destination_id, destination_con));
    State.add_edge(state, edge);
    switch (Hashtbl.find_opt(state.edge_map, patch.id)) {
    | Some(old_edge) =>
      switch (edge.sign, old_edge.sign) {
      | (Live, Live)
      | (Live, Dead)
      | (Dead, Dead) => ()
      | (Dead, Live) =>
        let num_parents =
          List.length(Node.live_parent_edges(destination_node));
        if (num_parents == 1) {
          {};
        };
      }
    | None =>
      switch (edge.sign) {
      | Dead => ()
      | Live =>
        // add nonexistent edge
        let num_parents =
          List.length(Node.live_parent_edges(destination_node));
        if (num_parents == 1) {
          destination_node.root = false;
          let root_of_source = root_of_node(state, source_node);
          if (root_of_source.id == destination_node.id) {
            roll(state, source_node);
          };
        } else if (num_parents == 2) {
          if (destination_node.part_of_unicycle) {
            unroll(state, destination_node);
          };
          destination_node.root = true;
        };
      }
    };
  };
};
