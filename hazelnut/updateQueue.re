open Incremental;
open Monad_lib.Monad;
open Queue;
open Hazelnut;

module Update = {
  [@deriving sexp]
  type t =
    | NewSyn(Iexp.upper)
    | NewAna(Iexp.parent)
    | NewAnn(Iexp.upper)
    | NewAsc(Iexp.upper)
    | NewListRec(Iexp.upper)
    | NewY(Iexp.upper)
    | NewITE(Iexp.upper)
    | NewTypAp(Iexp.upper);

  let priority =
    fun
    | NewSyn(e) => snd(e.interval)
    | NewAna(e) => fst(child_of_parent(e).interval)
    | NewAnn(e) => fst(e.interval)
    | NewAsc(e) => fst(e.interval)
    | NewListRec(e) => fst(e.interval)
    | NewY(e) => fst(e.interval)
    | NewITE(e) => fst(e.interval)
    | NewTypAp(e) => fst(e.interval);

  // only called on updates with the same priority
  // NewAnn or NewAsc should always come first
  let compare_constructors = (update1, update2) =>
    switch (update1, update2) {
    | (NewAnn(_), _) => true
    | (NewAsc(_), _) => true
    | (_, NewAnn(_)) => false
    | (_, NewAsc(_)) => false
    | _ => true
    };

  let leq = (update1: t, update2: t): bool => {
    let comparison = compare(priority(update1), priority(update2));
    if (comparison == 0) {
      compare_constructors(update1, update2);
    } else {
      comparison < 0;
    };
  };
};

module UpdateQueue = {
  include PQueue(Update);

  let in_queue_parent: Iexp.parent => bool =
    fun
    | Deleted => true
    | Root(r) => r.in_queue_root.ana
    | Lower(e) => e.in_queue_lower.ana;

  let set_in_queue_parent = (b: bool): (Iexp.parent => unit) =>
    fun
    | Deleted => ()
    | Root(r) => r.in_queue_root.ana = b
    | Lower(e) => e.in_queue_lower.ana = b;

  let parent_deleted: Iexp.parent => bool =
    fun
    | Deleted => true
    | Root(_) => false
    | Lower(e) => e.deleted_lower;

  // Only pushes updates onto the queue if the corresponding
  // queue membership bit is false (so no duplicates). Sets this bit to true.
  let update_push = (u: Update.t, q: t): unit => {
    switch (u) {
    | NewSyn(e) when !e.in_queue_upper.syn =>
      e.in_queue_upper.syn = true;
      push(u, q);
    | NewAna(p) when !in_queue_parent(p) =>
      set_in_queue_parent(true, p);
      push(u, q);
    | NewAnn(e) when !e.in_queue_upper.ann =>
      e.in_queue_upper.ann = true;
      push(u, q);
    | NewAsc(e) when !e.in_queue_upper.asc =>
      e.in_queue_upper.asc = true;
      push(u, q);
    | NewListRec(e) when !e.in_queue_upper.list_rec =>
      e.in_queue_upper.list_rec = true;
      push(u, q);
    | NewY(e) when !e.in_queue_upper.y =>
      e.in_queue_upper.y = true;
      push(u, q);
    | NewITE(e) when !e.in_queue_upper.ite =>
      e.in_queue_upper.ite = true;
      push(u, q);
    | NewTypAp(e) when !e.in_queue_upper.typ_ap =>
      e.in_queue_upper.typ_ap = true;
      push(u, q);
    | _ => ()
    };
  };

  let update_push_list = (es: list(Update.t), q: t) => {
    List.iter(e => update_push(e, q), es);
  };

  let rec update_pop = (q: t): option(Update.t) => {
    let recurse_if_deleted = (deleted, u) =>
      if (deleted) {
        update_pop(q);
      } else {
        Some(u);
      };
    // Asserts that the queue membership bit is true when popping,
    // and sets this bit to false. If the popped update is in a deleted
    // subterm, throw it away and keep popping.
    let* u = pop(q);
    switch (u) {
    | NewSyn(e) =>
      assert(e.in_queue_upper.syn);
      e.in_queue_upper.syn = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewAna(p) =>
      assert(in_queue_parent(p));
      set_in_queue_parent(false, p);
      recurse_if_deleted(parent_deleted(p), u);
    | NewAnn(e) =>
      assert(e.in_queue_upper.ann);
      e.in_queue_upper.ann = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewAsc(e) =>
      assert(e.in_queue_upper.asc);
      e.in_queue_upper.asc = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewListRec(e) =>
      assert(e.in_queue_upper.list_rec);
      e.in_queue_upper.list_rec = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewY(e) =>
      assert(e.in_queue_upper.y);
      e.in_queue_upper.y = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewITE(e) =>
      assert(e.in_queue_upper.ite);
      e.in_queue_upper.ite = false;
      recurse_if_deleted(e.deleted_upper, u);
    | NewTypAp(e) =>
      assert(e.in_queue_upper.typ_ap);
      e.in_queue_upper.typ_ap = false;
      recurse_if_deleted(e.deleted_upper, u);
    };
  };
  let update_ana =
      (lower: Iexp.lower, t_new: option(Htyp.t)): list(Update.t) =>
    if (t_new == lower.ana) {
      [];
    } else {
      lower.ana = t_new;
      [Update.NewAna(Lower(lower))];
    };

  let update_syn =
      (upper: Iexp.upper, t_new: option(Htyp.t)): list(Update.t) =>
    if (t_new == upper.syn) {
      [];
    } else {
      upper.syn = t_new;
      [Update.NewSyn(upper)];
    };
};
