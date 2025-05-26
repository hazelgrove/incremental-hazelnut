open Node;
// open Typ;
// open Monad_lib.Monad;
open Queue;

module Update = {
  // [@deriving sexp]
  type t =
    | NewSyn(Node.t)
    | NewAna(Node.t)
    | NewTyp(Node.t);
  // imprecision: NewTyp should trigger asap.
  let priority =
    fun
    | NewSyn(e) => snd(e.interval)
    | NewAna(e) => fst(e.interval)
    | NewTyp(e) => fst(e.interval);
  let leq = (update1: t, update2: t): bool => {
    compare(priority(update1), priority(update2)) < 0;
  };
};
module UpdateQueue = {
  include PQueue(Update);
  //   let get_dirty_ana = (e: Node.t) => {
  //     Node.get_ana(e);
  //   };
  //   let set_dirty_ana = (e: Node.t, b: bool) => {
  //     Node.set_ana(e, (fst(Node.get_ana(e)), b));
  //   };
  //   let get_dirty_syn = (e: Node.t) => {
  //     snd(Node.get_syn(e));
  //   };
  //   let set_dirty_syn = (e: Node.t, b: bool) => {
  //     Node.set_syn(e, (fst(Node.get_syn(e)), b));
  //   };
  //   // Only pushes updates onto the queue if the corresponding
  //   // queue membership bit is false (so no duplicates). Sets this bit to true.
  //   let update_push = (u: Update.t, q: t): unit => {
  //     switch (u) {
  //     | NewSyn(e) when !get_dirty_syn(e) =>
  //       set_dirty_syn(e, true);
  //       push(u, q);
  //     | NewSyn(_) => ()
  //     | NewAna(e) when !get_dirty_ana(e) =>
  //       set_dirty_ana(e, true);
  //       push(u, q);
  //     | NewAna(_) => ()
  //     | NewTyp(e) when !Node.get_typ_dirtiness(e) =>
  //       Node.set_typ_dirtiness(e, true);
  //       push(u, q);
  //     | NewTyp(_) => ()
  //     };
  //   };
  //   let update_push_list = (es: list(Update.t), q: t) => {
  //     List.iter(e => update_push(e, q), es);
  //   };
  //   let rec update_pop = (q: t): option(Update.t) => {
  //     let recurse_if_deleted = (deleted, u) =>
  //       if (deleted) {
  //         update_pop(q);
  //       } else {
  //         Some(u);
  //       };
  //     // Asserts that the queue membership bit is true when popping,
  //     // and sets this bit to false. If the popped update is in a deleted
  //     // subterm, throw it away and keep popping.
  //     let* u = pop(q);
  //     switch (u) {
  //     | NewSyn(e) =>
  //       assert(get_dirty_syn(e));
  //       set_dirty_syn(e, false);
  //       recurse_if_deleted(e.deleted, u);
  //     | NewAna(e) =>
  //       assert(get_dirty_ana(e));
  //       set_dirty_ana(e, false);
  //       recurse_if_deleted(e.deleted, u);
  //     | NewTyp(e) =>
  //       assert(Node.get_typ_dirtiness(e));
  //       Node.set_typ_dirtiness(e, false);
  //       recurse_if_deleted(e.deleted, u);
  //     };
  //   };
  //   let update_ana = (e: Node.t, t_new: option(Typ.t)): list(Update.t) =>
  //     if (t_new == fst(Node.get_ana(e))) {
  //       [];
  //     } else {
  //       Node.set_ana(e, (t_new, true));
  //       [Update.NewSyn(e)];
  //     };
  //   let update_syn = (e: Node.t, t_new: option(Typ.t)): list(Update.t) =>
  //     if (t_new == fst(Node.get_syn(e))) {
  //       [];
  //     } else {
  //       Node.set_syn(e, (t_new, true));
  //       [Update.NewSyn(e)];
  //     };
};
