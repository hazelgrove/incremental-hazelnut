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

let initial_exp = exp_hole_upper(initial_interval);

let initial_root: Iexp.parent = {
  let r: Iexp.root = {
    root_child: initial_exp,
    in_queue_root: InQueue.default_root(),
  };
  initial_exp.parent = Root(r);
  Root(r);
};
let initial_cursor: Icursor.t = CursorExp(initial_exp);
let initial_state: Istate.t = {c: initial_cursor, q: UpdateQueue.empty};
