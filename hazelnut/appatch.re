open Patch;
open Node;
open State;

let rec root_of_term = (state: State.t, e: Node.t) => {
  switch (get_parent(state, e)) {
  | None => e
  | Some(parent) => root_of_term(state, parent)
  };
};

let edge_of_patch = (patch: Patch.t): Node.edge => {
  let ((source_id, _source_con), source_location) = patch.source;
  let (destination_id, _destination_con) = patch.destination;
  let edge: Node.edge = {
    id: patch.id,
    source: (source_id, source_location),
    destination: destination_id,
    sign: patch.sign,
    meta: patch.meta,
  };
  edge;
};

let create_if_new = (state: State.t, node: Patch.node): unit => {
  let (id, con) = node;
  switch (Hashtbl.find_opt(state.term_map, id)) {
  | Some(_) => ()
  | None =>
    let create_con = (c: Patch.content): Node.content => {
      switch (c) {
      | Pat(Var(x)) => Pat(Var(x))
      | Typ(Arrow) => Typ(failwith("todo"), Arrow)
      | Exp(Var(x)) => Exp(failwith("todo"), Var(failwith("todo"), x))
      | Exp(Fun(x)) => Exp(failwith("todo"), Fun(failwith("todo"), x))
      | Exp(Ap) => Exp(failwith("todo"), Ap)
      };
    };
    let n = Node.create_node(id, create_con(con));
    Hashtbl.add(state.term_map, id, n);
  };
};

let rec appatch = (state: State.t, patch: Patch.t): State.t => {
  let ((source_id, source_con), _source_location) = patch.source;
  let (destination_id, destination_con) = patch.destination;
  switch (Hashtbl.find_opt(state.edge_map, patch.id)) {
  // edge ids are unique, so if this id is in the database, the patch must have already been applied.
  | Some(_) => state
  | None =>
    // if the patch is new, make an edge and add it to the database.
    let edge = edge_of_patch(patch);
    Hashtbl.add(state.edge_map, patch.id, edge);
    // if the nodes haven't been seen before, make them
    create_if_new(state, (source_id, source_con));
    create_if_new(state, (destination_id, destination_con));
    switch (Hashtbl.find_opt(state.edge_map, patch.id)) {
    | Some(edge) =>
      switch (patch.sign, edge.sign) {
      | (Add, Add)
      | (Add, Delete)
      | (Delete, Delete) => state
      | (Delete, Add) => failwith("delete live edge")
      }
    | None =>
      switch (patch.sign) {
      | Delete =>
        // I don't think we need to make new nodes in this case, right?
        let edge = edge_of_patch(patch);
        Hashtbl.add(state.edge_map, patch.id, edge);
        state;
      | Add =>
        // add nonexistent edge
        let source_term =
          switch (Hashtbl.find_opt(state.term_map, source_id)) {
          | None => failwith("Todo")
          | Some(term) => term
          };
        let destination_term =
          switch (Hashtbl.find_opt(state.term_map, destination_id)) {
          | None => failwith("Todo")
          | Some(term) => term
          };
        let root_of_source = root_of_term(state, source_term);
        if (root_of_source.id == destination_term.id) {
          failwith("first case");
        } else if (destination_term.part_of_unicycle) {
          failwith("second case");
        } else {
          failwith("normal add cases");
        };
        state;
      }
    };
  // let ((source_id, source_con), source_child) = patch.source;
  // let (destination_id, destination_con) = patch.destination;
  // let source_term =
  //   switch (Hashtbl.find_opt(state.id_map, source_id)) {
  //   | None => failwith("Todo")
  //   | Some(term) => term
  //   };
  // let destination_term =
  //   switch (Hashtbl.find_opt(state.id_map, destination_id)) {
  //   | None => failwith("Todo")
  //   | Some(term) => term
  //   };
  // switch (patch.sign) {
  // | Add =>
  //   let root_of_source = root_of_term(source_term);
  //   if (root_of_source.id == destination_term.id) {
  //     failwith("first case");
  //   } else if (destination_term.part_of_unicycle) {
  //     failwith("second case");
  //   } else {
  //     failwith("normal add cases");
  //   };
  // | Delete => {}
  // };
  };
};
