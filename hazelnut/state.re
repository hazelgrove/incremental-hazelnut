open Hazelnut;
open Incremental;
open UpdateQueue;

module Icursor = {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t)
    | CursorBind(Iexp.upper);
};

module Istate = {
  [@deriving sexp]
  type t = {
    c: Icursor.t,
    q: UpdateQueue.t,
  };
};

let initial_root_and_state = (): (Iexp.parent, Istate.t) => {
  let initial_exp = exp_hole_upper(initial_interval);
  let initial_cursor: Icursor.t = CursorExp(initial_exp);
  let r: Iexp.root = {
    root_child: initial_exp,
    in_queue_root: InQueue.default_root(),
  };
  let initial_root = Iexp.Root(r);
  initial_exp.parent = initial_root;
  let initial_state: Istate.t = {c: initial_cursor, q: UpdateQueue.empty};
  (initial_root, initial_state);
};
