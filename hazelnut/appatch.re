open Patch;
open Term;
open State;

let rec root_of_term = (e: Term.t) => {
  switch (e.parent) {
  | None => e
  | Some(parent) => root_of_term(parent)
  };
};

let rec appatch = (state: State.t, patch: Patch.t): State.t => {
  let ((source_id, source_con), source_child) = patch.source;
  let (destination_id, destination_con) = patch.destination;
  let source_term =
    switch (Hashtbl.find_opt(state.id_map, source_id)) {
    | None => failwith("Todo")
    | Some(term) => term
    };
  let destination_term =
    switch (Hashtbl.find_opt(state.id_map, destination_id)) {
    | None => failwith("Todo")
    | Some(term) => term
    };
  switch (patch.sign) {
  | Add =>
    let root_of_source = root_of_term(source_term);
    if (root_of_source.id == destination_term.id) {
      failwith("first case");
    } else if (destination_term.part_of_unicycle) {
      failwith("second case");
    } else {
      failwith("normal add cases");
    };
  | Delete => {}
  };
};
