open Hazelnut;
open Incremental;
open Tree;
open UpdateQueue;
open Sexplib.Std;
open Sexplib0;
open Order;

module Icursor = {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t)
    | CursorBind(Iexp.upper);
};

module BinderSet = {
  type t = Hashtbl.t((string, BinderKind.t), Tree.t(Iexp.upper));
  let sexp_of_t = _ => Sexp.Atom("unimplemented");
  let t_of_sexp = _ => failwith("BinderSet of sexp");
};

module Istate = {
  [@deriving sexp]
  type ephemeral = {
    root: Iexp.root,
    q: UpdateQueue.t,
    binder_set: BinderSet.t,
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
  // print_endline("initializing root and state");
  let a = Order.create();
  // print_endline(
  //   "initializing state with first OM: "
  //   ++ string_of_sexp(Order.sexp_of_t(a)),
  // );
  let b = Order.add_next(a);
  let initial_exp = exp_hole_upper((a, b));
  let initial_root: Iexp.root = {
    root_child: initial_exp,
    free_vars: Hashtbl.create(100),
    in_queue_root: InQueue.default_root(),
  };
  initial_exp.parent = Root(initial_root);

  let initial_queue = UpdateQueue.empty();

  let initial_ephemeral: Istate.ephemeral = {
    root: initial_root,
    q: initial_queue,
    binder_set: Hashtbl.create(100),
  };

  let initial_cursor: Icursor.t = CursorExp(initial_exp);
  let initial_persistent: Istate.persistent = {c: initial_cursor};
  {
    ephemeral: initial_ephemeral,
    persistent: initial_persistent,
  };
};
