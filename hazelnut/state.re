open Hazelnut;
open Incremental;
open Tree;
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
  type ephemeral = {
    root: Iexp.parent,
    q: UpdateQueue.t,
  };
  [@deriving sexp]
  type persistent = {c: Icursor.t};
  [@deriving sexp]
  type t = {
    ephemeral,
    persistent,
  };
};

let initial_state = (): Istate.t => {
  print_endline("initializing root and state");
  let initial_exp = exp_hole_upper(initial_interval);
  let r: Iexp.root = {
    root_child: initial_exp,
    free_vars: ref(Tree.empty),
    in_queue_root: InQueue.default_root(),
  };
  let initial_root = Iexp.Root(r);
  initial_exp.parent = initial_root;

  let initial_ephemeral: Istate.ephemeral = {
    root: initial_root,
    q: UpdateQueue.empty,
  };

  let initial_cursor: Icursor.t = CursorExp(initial_exp);
  let initial_persistent: Istate.persistent = {c: initial_cursor};
  {ephemeral: initial_ephemeral, persistent: initial_persistent};
};
