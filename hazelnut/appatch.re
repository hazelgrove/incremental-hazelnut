open Patch;
open Term;
open State;

let rec root_of_term = (e: Term.t) => {
  switch (e.parent) {
  | None => e
  | Some((parent, _)) => root_of_term(parent)
  };
};

let edge_of_patch = (patch: Patch.t): Term.edge => {
  let ((source_id, _source_con), source_location) = patch.source;
  let (destination_id, _destination_con) = patch.destination;
  let edge: Term.edge = {
    id: patch.id,
    source: (source_id, source_location),
    destination: destination_id,
    sign: patch.sign,
    meta: patch.meta,
  };
  edge;
};

let rec appatch = (state: State.t, patch: Patch.t): State.t => {
  let ((source_id, source_con), source_location) = patch.source;
  let (destination_id, destination_con) = patch.destination;
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
      let root_of_source = root_of_term(source_term);
      if (root_of_source.id == destination_term.id) {
        failwith("first case");
      } else if (destination_term.part_of_unicycle) {
        failwith("second case");
      } else {
        failwith("normal add cases");
      };
      state;
    }
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
