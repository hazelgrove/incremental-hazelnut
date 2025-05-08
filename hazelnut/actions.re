open Sexplib.Std;
open Id;
open Order;
open Tree;
open Term;
open State;
open UpdateQueue;

// open Monad_lib.Monad;

let _string_of_interval = (i: (Order.t, Order.t)) =>
  "("
  ++ string_of_sexp(Order.sexp_of_t(fst(i)))
  ++ " , "
  ++ string_of_sexp(Order.sexp_of_t(snd(i)))
  ++ ")";

type child = int;

module Action = {
  // [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(child)
    | Delete
    | WrapArrow(child)
    | InsertVar(string)
    | WrapLam
    | WrapAp(child)
    | Unwrap(child);
};

let replace_child_in_parent = (child, child', parent: Term.t): unit => {
  let replace_child = (child: Term.t, child': Term.t, parent_child: Term.t) =>
    if (parent_child.id == child.id) {
      child';
    } else {
      parent_child;
    };
  parent.children = List.map(replace_child(child, child'), parent.children);
};

let replace = (e: Term.t, e': Term.t): unit => {
  e'.parent = e.parent;
  Option.iter(replace_child_in_parent(e, e'), e.parent);
  e.parent = None;
};

// let splice = (new_lower: Iexp.lower, new_upper: Iexp.upper): unit => {
//   new_lower.upper = new_upper; //skip up
//   set_child_in_parent(new_upper.parent, new_upper); //fix parent
//   new_lower.child.parent = Lower(new_lower); //fix child
// };

// let upper_of_parent = (p: Iexp.parent): option(Iexp.upper) => {
//   switch (p) {
//   | Deleted
//   | Root(_) => None
//   | Lower(r) => Some(r.upper)
//   };
// };

// let var_set_of_binder = (x: string): (Iexp.parent => Iexp.var_set) =>
//   fun
//   | Deleted => failwith("var set of deleted root")
//   | Root(root) => {
//       switch (Hashtbl.find_opt(root.free_vars, x)) {
//       | None =>
//         let new_set = ref(Tree.empty);
//         Hashtbl.add(root.free_vars, x, new_set);
//         new_set;
//       | Some(var_set) => var_set
//       };
//     }
//   | Lower(lower) =>
//     switch (lower.upper.middle) {
//     | Lam(_, _, _, _, _, bound_vars) => bound_vars
//     | _ => failwith("non-lam binder")
//     };

// let name_of_var_upper = (e: Iexp.upper): string =>
//   switch (e.middle) {
//   | Var(x, _, _) => x
//   | _ => failwith("name_of_var_upper called on non-var")
//   };

// let unbind_from_binder = (var: Iexp.upper, parent: Iexp.parent) => {
//   Iexp.remove_bound_var(
//     var,
//     var_set_of_binder(name_of_var_upper(var), parent),
//   );
// };

// let bind_to_binder = (var: Iexp.upper, parent: Iexp.parent) => {
//   // print_endline("adding to binder");
//   Iexp.add_bound_var(
//     var,
//     var_set_of_binder(name_of_var_upper(var), parent),
//     // print_endline(
//     //   "now has this many: "
//     //   ++ string_of_int(
//     //        List.length(
//     //          Tree.list_of_t(
//     //            var_set_of_binder(name_of_var_upper(var), parent).contents,
//     //          ),
//     //        ),
//     //      ),
//     // );
//   );
// };

// // precondition: e.middle is a Var
// // makes them all synthesize [syn], marks them all as [m], and updates their
// // binding on both ends. It also marks them as on the update queue with new syn.
// let update_var =
//     (e: Iexp.upper, syn: Htyp.t, new_mark: Mark.t, new_binder: Iexp.binder)
//     : unit => {
//   switch (e.middle) {
//   | Var(_, mark, binder) =>
//     // remove this var from its previous binder
//     unbind_from_binder(e, binder.contents);
//     // set the local binder, mark, and syn type
//     binder.contents = new_binder;
//     mark.contents = new_mark;
//     e.syn = Some(syn);
//   | _ => failwith("update_var called on non-var")
//   };
// };

// // Finds the looks up [name] in the context of [e].
// // Returns the binding site (or root), the synthesized type, and whether [name] is free.
// let look_up_binder =
//     (x: string, e: Iexp.upper, binder_set: BinderSet.t, root: Iexp.root)
//     : (Iexp.parent, Htyp.t, Mark.t) => {
//   let free: (Iexp.parent, Htyp.t, Mark.t) = (Root(root), Hole, Marked);
//   switch (Hashtbl.find_opt(binder_set, x)) {
//   | None => free
//   | Some(x_binder_set) =>
//     // print_endline(
//     //   "finding container for: " ++ _string_of_interval(e.interval),
//     // );
//     switch (Tree.splay_tightest(e.interval, x_binder_set)) {
//     | None => free
//     | Some((upper, splayed)) =>
//       Hashtbl.replace(binder_set, x, splayed);
//       // print_endline(
//       //   "found container: " ++ _string_of_interval(upper.interval),
//       // );
//       switch (upper.entry.middle) {
//       | Lam(bind, t, _, _, body, _) when Bind.Var(x) == bind.contents => (
//           Lower(body),
//           t.contents,
//           Unmarked,
//         )
//       | _ => failwith("invalid binder lookup")
//       };
//     }
//   };
// };

// // Dumb version of look_up_binder for comparison
// let rec _look_up_binder_walk =
//         (parent: Iexp.parent, name: string): (Iexp.parent, Htyp.t, Mark.t) => {
//   switch (parent) {
//   | Deleted
//   | Root(_) => (parent, Hole, Marked)
//   | Lower(lower) =>
//     switch (lower.upper.middle) {
//     | Lam(bind, lam_ty, _, _, _, _) =>
//       if (bind.contents == Var(name)) {
//         (parent, lam_ty.contents, Unmarked);
//       } else {
//         _look_up_binder_walk(lower.upper.parent, name);
//       }
//     | _ => _look_up_binder_walk(lower.upper.parent, name)
//     }
//   };
// };

// let add_bound_var_set =
//     (x: string, joining_set: Tree.t(Iexp.upper), binder: Iexp.parent) => {
//   let parent_var_set = var_set_of_binder(x, binder);
//   Iexp.union_bound_vars(joining_set, parent_var_set);
// };

// let capture_name =
//     (x: string, e: Iexp.upper, binder_set: BinderSet.t, root: Iexp.root) => {
//   let (ancestor_binder, _, _) = look_up_binder(x, e, binder_set, root);
//   // print_endline("capturing name: " ++ x);
//   // switch (ancestor_binder) {
//   // | Root(_) => print_endline("it was free before")
//   // | _ => print_endline("it was bound before")
//   // };
//   let found_vars = var_set_of_binder(x, ancestor_binder);
//   // print_endline(
//   //   "this many in parental scope: "
//   //   ++ string_of_int(List.length(Tree.list_of_t(found_vars.contents))),
//   // );
//   // let intervals =
//   //   List.map(
//   //     (upper: Iexp.upper) => string_of_interval(upper.interval),
//   //     Tree.list_of_t(found_vars.contents),
//   //   );
//   // print_endline("parent var intervals: " ++ String.concat(", ", intervals));
//   // print_endline("excising interval: " ++ string_of_interval(e.interval));
//   let excised_vars = Iexp.excise_bound_vars(e.interval, found_vars);
//   // print_endline(
//   //   "this many excised: "
//   //   ++ string_of_int(List.length(Tree.list_of_t(excised_vars))),
//   // );
//   // print_endline(
//   //   "now this many in parental scope: "
//   //   ++ string_of_int(List.length(Tree.list_of_t(found_vars.contents))),
//   // );
//   excised_vars;
// };

// // Dumb version of capture_name for comparison
// let rec _capture_name_body =
//         (e: Iexp.upper, name: string, syn: Htyp.t, binder: Iexp.binder)
//         : list(Iexp.upper) => {
//   switch (e.middle) {
//   | EHole
//   | NumLit(_) => []
//   | Var(var_name, _, _) =>
//     if (name == var_name) {
//       update_var(e, syn, Unmarked, binder);
//       [e];
//     } else {
//       [];
//     }
//   | Lam(bind, _, _, _, body_lower, _) =>
//     if (bind.contents == Var(name)) {
//       [];
//     } else {
//       _capture_name_body(body_lower.child, name, syn, binder);
//     }
//   | Asc(lower, _) => _capture_name_body(lower.child, name, syn, binder)
//   | Plus(lower_a, lower_b) =>
//     List.append(
//       _capture_name_body(lower_a.child, name, syn, binder),
//       _capture_name_body(lower_b.child, name, syn, binder),
//     )
//   | Ap(actor, _, param) =>
//     List.append(
//       _capture_name_body(actor.child, name, syn, binder),
//       _capture_name_body(param.child, name, syn, binder),
//     )
//   | Pair(lower_a, lower_b, _) =>
//     List.append(
//       _capture_name_body(lower_a.child, name, syn, binder),
//       _capture_name_body(lower_b.child, name, syn, binder),
//     )
//   | Proj(_, lower, _) => _capture_name_body(lower.child, name, syn, binder)
//   | _ => failwith("unimplemented")
//   };
// };

// let remove_from_binder_set =
//     (x: string, e: Iexp.upper, binder_set: BinderSet.t) => {
//   switch (Hashtbl.find_opt(binder_set, x)) {
//   | None => failwith("removing binder that doesn't exist")
//   | Some(var_set) =>
//     let new_set = Tree.delete(fst(e.interval), var_set);
//     if (Tree.is_empty(new_set)) {
//       Hashtbl.remove(binder_set, x);
//     } else {
//       Hashtbl.replace(binder_set, x, new_set);
//     };
//   };
// };

// let add_to_binder_set = (x: string, e: Iexp.upper, binder_set: BinderSet.t) => {
//   // print_endline("adding binder at: " ++ _string_of_interval(e.interval));
//   switch (Hashtbl.find_opt(binder_set, x)) {
//   | None =>
//     let new_set =
//       Tree.insert(e, fst(e.interval), snd(e.interval), Tree.empty);
//     Hashtbl.add(binder_set, x, new_set);
//   | Some(x_binder_set) =>
//     let new_x_binder_set =
//       Tree.insert(e, fst(e.interval), snd(e.interval), x_binder_set);
//     Hashtbl.replace(binder_set, x, new_x_binder_set);
//   };
// };

let rec delete_subterm = (e: Term.t) => {
  e.deleted = true;
  List.iter(delete_subterm, e.children);
};

let interval_around = (e: Term.t) => {
  let (b, c) = e.interval;
  let a = Order.add_prev(b);
  let d = Order.add_next(c);
  // a < b < c < d
  assert(Order.lt(a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, d));
  (a, d);
};

let interval_after = (e: Term.t) => {
  let (_a, b) = e.interval;
  let c = Order.add_next(b);
  let d = Order.add_next(c);
  // a < b < c < d
  assert(Order.lt(_a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, d));
  (c, d);
};

let interval_before = (e: Term.t) => {
  let (c, _d) = e.interval;
  let b = Order.add_prev(c);
  let a = Order.add_prev(b);
  // a < b < c < d
  assert(Order.lt(a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, _d));
  (a, b);
};

// these belong in Pexp, copied for convenience

// let _string_of_child: Child.t => string =
//   fun
//   | One => "One"
//   | Two => "Two"
//   | Three => "Three";

// let _string_of_action: Action.t => string =
//   fun
//   | MoveUp => "MoveUp"
//   | MoveDown(c) => "MoveDown(" ++ _string_of_child(c) ++ ")"
//   | Delete => "Delete"
//   | WrapArrow(c) => "WrapArrow(" ++ _string_of_child(c) ++ ")"
//   | InsertVar(s) => "InsertVar(\"" ++ s ++ "\")"
//   | WrapAp(c) => "WrapAp(" ++ _string_of_child(c) ++ ")"
//   | WrapLam => "WrapLam"
//   | Unwrap(c) => "Unwrap(" ++ _string_of_child(c) ++ ")";

let initialize_id = (e: Term.t, id_map: IdMap.t, counter: Id.counter): unit => {
  let id = Id.fresh(counter);
  e.id = id;
  Hashtbl.add(id_map, id, e);
};

let delete_binder = (name: string, e: Term.t, binder_set: BinderSet.t): unit => {
  failwith(
    "Todo",
    // remove_from_binder_set(x, e, binder_set);
    //       let bound_var_set = bound_vars.contents;
    //       let (new_binder, t, m) = look_up_binder(x, e, binder_set, root);
    //       add_bound_var_set(x, bound_var_set, new_binder);
    //       let update = var => update_var(var, t, m, new_binder);
    //       Tree.iter(update, bound_var_set);
    //       let bound_var_list = Tree.list_of_t(bound_var_set);
    //       let update_list =
    //         [Update.NewAna(e.parent)]
    //         @ List.map(e => Update.NewSyn(e), bound_var_list)
    //         @ [NewAna(Lower(body)), NewSyn(body.child)];
    //       UpdateQueue.update_push_list(update_list, q);
    //       no_movement;
  );
};

let rec apply_action = (state: State.t, action: Action.t): State.t => {
  let return_noop: State.t = state;
  let return_cursor = (cursor: Term.t): State.t => {...state, cursor};

  switch (action) {
  | MoveUp =>
    switch (state.cursor.parent) {
    | None => return_noop
    | Some(parent) => return_cursor(parent)
    }
  | MoveDown(child) =>
    switch (List.nth_opt(state.cursor.children, child)) {
    | None => return_noop
    | Some(child) => return_cursor(child)
    }
  | Delete =>
    let new_term: Term.t = {
      id: (-1),
      interval: state.cursor.interval,
      deleted: false,
      parent: state.cursor.parent,
      edges: state.cursor.edges,
      content: state.cursor.content,
      children: [],
      marks: [],
    };
    initialize_id(new_term, state.id_map, state.counter);
    replace(state.cursor, new_term);
    delete_subterm(state.cursor);
    switch (state.cursor.content) {
    | Exp(_, exp_data) =>
      new_term.content = Exp(Hole, {...exp_data, syn: (Some(Hole), false)})
    | Typ(_, typ_data) =>
      new_term.content = Typ(Hole, {...typ_data, pure_typ: Hole})
    | Pat(Hole) => ()
    | Pat(Var(x)) =>
      new_term.content = Pat(Hole);
      delete_binder(x, Option.get(state.cursor.parent), state.binders);
    };
    UpdateQueue.update_push_list([NewAna(state.cursor)], state.queue);
    return_cursor(new_term);
  | WrapArrow(child) =>
    if (!(0 <= child && child < 2)) {
      return_noop;
    } else {
      let new_interval_arrow = interval_around(state.cursor);
      let new_interval_hole =
        if (child == 0) {
          interval_around(state.cursor);
        } else {
          interval_before(state.cursor);
        };
      let new_term_arrow: Term.t = {
        id: (-1),
        interval: new_interval_arrow,
        deleted: false,
        parent: state.cursor.parent,
        edges: state.cursor.edges,
        content: state.cursor.content,
        children: [],
        marks: [],
      };
      let new_term_hole: Term.t = {
        id: (-1),
        interval: new_interval_hole,
        deleted: false,
        parent: Some(new_term_arrow),
        edges: [], // todo
        content: state.cursor.content,
        children: [],
        marks: [],
      };
      initialize_id(new_term_arrow, state.id_map, state.counter);
      initialize_id(new_term_hole, state.id_map, state.counter);
      replace(state.cursor, new_term_arrow);
      state.cursor.parent = Some(new_term_arrow);
      if (child == 0) {
        new_term_arrow.children = [state.cursor, new_term_hole];
      } else {
        new_term_arrow.children = [new_term_hole, state.cursor];
      };
      ();
    }
  | InsertVar(string) => failwith("unimplemented")
  | WrapLam => failwith("unimplemented")
  | WrapAp(child) => failwith("unimplemented")
  | Unwrap(child) => failwith("unimplemented")
  };
  // | (CursorBind(e), MoveUp) => return_cursor(CursorExp(e))
  // | (CursorBind(e), Delete) =>
  //   switch (e.middle) {
  //   | Lam(bind, _t, _m1, _m2, body, bound_vars) =>
  //     switch (bind.contents) {
  //     | Var(x) =>
  //       bind.contents = Hole;
  //       remove_from_binder_set(x, e, binder_set);
  //       let bound_var_set = bound_vars.contents;
  //       let (new_binder, t, m) = look_up_binder(x, e, binder_set, root);
  //       add_bound_var_set(x, bound_var_set, new_binder);
  //       let update = var => update_var(var, t, m, new_binder);
  //       Tree.iter(update, bound_var_set);
  //       let bound_var_list = Tree.list_of_t(bound_var_set);
  //       let update_list =
  //         [Update.NewAna(e.parent)]
  //         @ List.map(e => Update.NewSyn(e), bound_var_list)
  //         @ [NewAna(Lower(body)), NewSyn(body.child)];
  //       UpdateQueue.update_push_list(update_list, q);
  //       no_movement;
  //     | Hole => no_movement
  //     }
  //   | _ => failwith("CursorBind on non lambda")
  //   }
  // | (CursorBind(e), InsertVar(x)) =>
  //   switch (e.middle) {
  //   | Lam(bind, t, _m1, _m2, body, bound_vars) =>
  //     switch (bind.contents) {
  //     | Hole =>
  //       bind.contents = Var(x);
  //       add_to_binder_set(x, e, binder_set);
  //       bound_vars.contents = capture_name(x, e, binder_set, root);
  //       let update = var =>
  //         update_var(var, t.contents, Unmarked, Iexp.Lower(body));
  //       Tree.iter(update, bound_vars.contents);
  //       let newly_bound_list = Tree.list_of_t(bound_vars.contents);
  //       let update_list =
  //         [Update.NewAna(e.parent)]
  //         @ List.map(e => Update.NewSyn(e), newly_bound_list)
  //         @ [NewAna(Lower(body)), NewSyn(body.child)];
  //       UpdateQueue.update_push_list(update_list, q);
  //       no_movement;
  //     | Var(_) => no_movement
  //     }
  //   | _ => failwith("CursorBind on non lambda")
  //   }
  // | (CursorBind(_), _) => no_movement
  // | (CursorTyp(e, Cursor(_)), MoveUp) => return_cursor(CursorExp(e))
  // | (CursorTyp(e, z), a) =>
  //   switch (e.middle) {
  //   | Lam(_, t, _m1, _m2, _body, _bound) =>
  //     let z' = apply_action_typ(z, a);
  //     let t' = erase_typ(z');
  //     t.contents = t';
  //     UpdateQueue.update_push(NewAnn(e), q);
  //     return_cursor(CursorTyp(e, z'));
  //   | Asc(_, t) =>
  //     let z' = apply_action_typ(z, a);
  //     let t' = erase_typ(z');
  //     t.contents = t';
  //     UpdateQueue.update_push(NewAsc(e), q);
  //     return_cursor(CursorTyp(e, z'));
  //   | ListRec(t) =>
  //     let z' = apply_action_typ(z, a);
  //     let t' = erase_typ(z');
  //     t.contents = t';
  //     UpdateQueue.update_push(NewListRec(e), q);
  //     return_cursor(CursorTyp(e, z'));
  //   | Y(t) =>
  //     let z' = apply_action_typ(z, a);
  //     let t' = erase_typ(z');
  //     t.contents = t';
  //     UpdateQueue.update_push(NewY(e), q);
  //     return_cursor(CursorTyp(e, z'));
  //   | _ => failwith("CursorTyp on node with no type")
  //   }
  // | (CursorExp(e), MoveUp) =>
  //   switch (upper_of_parent(e.parent)) {
  //   | None => no_movement
  //   | Some(e') => return_cursor(CursorExp(e'))
  //   }
  // | (CursorExp(e), MoveDown(child)) =>
  //   switch (e.middle) {
  //   | Var(_, _, _)
  //   | NumLit(_)
  //   | EHole
  //   | Nil
  //   | Cons => no_movement
  //   | Plus(e1, e2)
  //   | Pair(e1, e2, _)
  //   | Ap(e1, _, e2) =>
  //     switch (child) {
  //     | One => return_cursor(CursorExp(e1.child))
  //     | Two => return_cursor(CursorExp(e2.child))
  //     | Three => no_movement
  //     }
  //   | Lam(_, t, _, _, e1, _) =>
  //     switch (child) {
  //     | One => return_cursor(CursorBind(e))
  //     | Two => return_cursor(CursorTyp(e, Cursor(t.contents)))
  //     | Three => return_cursor(CursorExp(e1.child))
  //     }
  //   | Asc(e1, t) =>
  //     switch (child) {
  //     | One => return_cursor(CursorExp(e1.child))
  //     | Two => return_cursor(CursorTyp(e, Cursor(t.contents)))
  //     | Three => no_movement
  //     }
  //   | Proj(_, e, _) =>
  //     switch (child) {
  //     | One => return_cursor(CursorExp(e.child))
  //     | Two => no_movement
  //     | Three => no_movement
  //     }
  //   | ListRec(t) =>
  //     switch (child) {
  //     | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
  //     | Two
  //     | Three => no_movement
  //     }
  //   | Y(t) =>
  //     switch (child) {
  //     | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
  //     | Two
  //     | Three => no_movement
  //     }
  //   | ITE(t) =>
  //     switch (child) {
  //     | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
  //     | Two
  //     | Three => no_movement
  //     }
  //   }
  // | (CursorExp(e), Delete) =>
  //   let e': Iexp.upper = {
  //     parent: e.parent,
  //     syn: Some(Hole),
  //     middle: EHole,
  //     interval: e.interval,
  //     in_queue_upper: InQueue.default_upper(),
  //     deleted_upper: false,
  //   };
  //   delete_upper(e);
  //   replace(e, e');
  //   let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //   UpdateQueue.update_push_list(update_list, q);
  //   return_cursor(CursorExp(e'));
  // | (CursorExp(_), InsertNumType)
  // | (CursorExp(_), InsertBoolType)
  // | (CursorExp(_), InsertUnitType)
  // | (CursorExp(_), WrapArrow(_))
  // | (CursorExp(_), InsertList)
  // | (CursorExp(_), WrapProduct(_)) => no_movement
  // | (CursorExp(e), InsertNumLit(x)) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(Num),
  //       middle: NumLit(x),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertNil) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(List),
  //       middle: Nil,
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertCons) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(Arrow(Num, Arrow(List, List))),
  //       middle: Cons,
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertListRec) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn:
  //         Some(
  //           Arrow(
  //             Hole,
  //             Arrow(Arrow(Num, Arrow(Hole, Hole)), Arrow(List, Hole)),
  //           ),
  //         ),
  //       middle: ListRec(ref(Htyp.Hole)),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertListMatch) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn:
  //         Some(
  //           Arrow(
  //             List,
  //             Arrow(Hole, Arrow(Arrow(Num, Arrow(List, Hole)), Hole)),
  //           ),
  //         ),
  //       middle: ListRec(ref(Htyp.Hole)),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertY) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(Arrow(Arrow(Hole, Hole), Hole)),
  //       middle: Y(ref(Htyp.Hole)),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertLt) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(Arrow(Num, Arrow(Num, Bool))),
  //       middle: ListRec(ref(Htyp.Hole)),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertITE) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn:
  //         Some(
  //           Arrow(
  //             Bool,
  //             Arrow(Arrow(Unit, Hole), Arrow(Arrow(Unit, Hole), Hole)),
  //           ),
  //         ),
  //       middle: ListRec(ref(Htyp.Hole)),
  //       interval: e.interval,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     delete_upper(e);
  //     replace(e, e');
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), InsertVar(x)) =>
  //   switch (e.middle) {
  //   | EHole =>
  //     let (parent, ty, mark) = look_up_binder(x, e, binder_set, root);
  //     let e': Iexp.upper = {
  //       parent: e.parent,
  //       syn: Some(ty),
  //       interval: e.interval,
  //       middle: Var(x, ref(mark), ref(parent)),
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     // switch (parent) {
  //     // | Root(_) => print_endline("isnerting to root")
  //     // | _ => print_endline("inserting ound")
  //     // };
  //     delete_upper(e);
  //     replace(e, e');
  //     bind_to_binder(e', parent);
  //     let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(e'));
  //   | _ => no_movement
  //   }
  // | (CursorExp(e), WrapPlus(child)) =>
  //   let make_plus_with_children = (parent, interval, e1, e2, q) => {
  //     let new_lower_left: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: Some(Num),
  //       marked: Unmarked,
  //       child: e1,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_lower_right: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: Some(Num),
  //       marked: Unmarked,
  //       child: e2,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
  //     let new_upper: Iexp.upper = {
  //       parent,
  //       syn: Some(Num),
  //       interval,
  //       middle: new_mid,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     splice(new_lower_left, new_upper);
  //     splice(new_lower_right, new_upper);
  //     let update_list = [
  //       Update.NewAna(parent),
  //       Update.NewAna(Lower(new_lower_left)),
  //       Update.NewAna(Lower(new_lower_right)),
  //       Update.NewSyn(new_upper),
  //     ];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(new_upper));
  //   };
  //   let interval = interval_around(e);
  //   switch (child) {
  //   | One =>
  //     let hole = exp_hole_upper(interval_after(e));
  //     make_plus_with_children(e.parent, interval, e, hole, q);
  //   | Two =>
  //     let hole = exp_hole_upper(interval_before(e));
  //     make_plus_with_children(e.parent, interval, hole, e, q);
  //   | Three => no_movement
  //   };
  // | (CursorExp(e), WrapAp(child)) =>
  //   let make_ap_with_children = (parent, interval, e1, e2, q) => {
  //     let new_lower_left: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: None,
  //       marked: Unmarked,
  //       child: e1,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_lower_right: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: Some(Hole),
  //       marked: Unmarked,
  //       child: e2,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_mid: Iexp.middle =
  //       Ap(new_lower_left, ref(Mark.Unmarked), new_lower_right);
  //     let new_upper: Iexp.upper = {
  //       parent,
  //       syn: Some(Hole),
  //       interval,
  //       middle: new_mid,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     splice(new_lower_left, new_upper);
  //     splice(new_lower_right, new_upper);
  //     let update_list = [
  //       Update.NewAna(new_upper.parent),
  //       Update.NewSyn(e1),
  //       Update.NewSyn(new_upper),
  //       switch (child) {
  //       | Child.One => Update.NewAna(Lower(new_lower_left))
  //       | Child.Two => Update.NewAna(Lower(new_lower_right))
  //       | Child.Three => raise(Unreachable)
  //       },
  //     ];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(new_upper));
  //   };
  //   // this must come before the calls to interval_before or _after. It mutates s.som.
  //   let interval = interval_around(e);
  //   switch (child) {
  //   | One =>
  //     let hole = exp_hole_upper(interval_after(e));
  //     make_ap_with_children(e.parent, interval, e, hole, q);
  //   | Two =>
  //     let hole = exp_hole_upper(interval_before(e));
  //     make_ap_with_children(e.parent, interval, hole, e, q);
  //   | Three => no_movement
  //   };
  // | (CursorExp(body), WrapLam) =>
  //   let new_lower: Iexp.lower = {
  //     upper: dummy_upper(),
  //     ana: None,
  //     marked: Unmarked,
  //     child: body,
  //     in_queue_lower: InQueue.default_lower(),
  //     deleted_lower: false,
  //   };
  //   let new_mid =
  //     Iexp.Lam(
  //       ref(Bind.Hole),
  //       ref(Htyp.Hole),
  //       ref(Mark.Unmarked),
  //       ref(Mark.Unmarked),
  //       new_lower,
  //       ref(Tree.empty),
  //     );
  //   let new_upper: Iexp.upper = {
  //     parent: body.parent,
  //     syn: None,
  //     interval: interval_around(body),
  //     middle: new_mid,
  //     in_queue_upper: InQueue.default_upper(),
  //     deleted_upper: false,
  //   };
  //   splice(new_lower, new_upper);
  //   let update_list = [
  //     Update.NewAna(new_upper.parent),
  //     Update.NewAna(Lower(new_lower)),
  //     Update.NewSyn(body),
  //     Update.NewSyn(new_upper),
  //   ];
  //   UpdateQueue.update_push_list(update_list, q);
  //   return_cursor(CursorExp(new_upper));
  // | (CursorExp(e), WrapPair(child)) =>
  //   let make_product_with_children = (parent, interval, e1, e2, q, child) => {
  //     let new_lower_left: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: None,
  //       marked: Unmarked,
  //       child: e1,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_lower_right: Iexp.lower = {
  //       upper: dummy_upper(),
  //       ana: None,
  //       marked: Unmarked,
  //       child: e2,
  //       in_queue_lower: InQueue.default_lower(),
  //       deleted_lower: false,
  //     };
  //     let new_mid: Iexp.middle =
  //       Pair(new_lower_left, new_lower_right, ref(Mark.Unmarked));
  //     let new_upper: Iexp.upper = {
  //       parent,
  //       syn: None,
  //       interval,
  //       middle: new_mid,
  //       in_queue_upper: InQueue.default_upper(),
  //       deleted_upper: false,
  //     };
  //     splice(new_lower_left, new_upper);
  //     splice(new_lower_right, new_upper);
  //     let update_list = [
  //       Update.NewAna(parent),
  //       Update.NewSyn(e1),
  //       Update.NewSyn(e2),
  //       Update.NewSyn(new_upper),
  //       switch (child) {
  //       | Child.One => Update.NewAna(Lower(new_lower_left))
  //       | Child.Two => Update.NewAna(Lower(new_lower_right))
  //       | Child.Three => raise(Unreachable)
  //       },
  //     ];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(new_upper));
  //   };
  //   let interval = interval_around(e);
  //   switch (child) {
  //   | One =>
  //     let hole = exp_hole_upper(interval_after(e));
  //     make_product_with_children(e.parent, interval, e, hole, q, Child.One);
  //   | Two =>
  //     let hole = exp_hole_upper(interval_before(e));
  //     make_product_with_children(e.parent, interval, hole, e, q, Child.Two);
  //   | Three => no_movement
  //   };
  // | (CursorExp(e), WrapProj(prod_side)) =>
  //   let parent = e.parent;
  //   let interval = interval_around(e);
  //   let new_lower: Iexp.lower = {
  //     upper: dummy_upper(),
  //     ana: None,
  //     marked: Unmarked,
  //     child: e,
  //     in_queue_lower: InQueue.default_lower(),
  //     deleted_lower: false,
  //   };
  //   let new_middle: Iexp.middle =
  //     Proj(prod_side, new_lower, ref(Mark.Unmarked));
  //   let new_upper: Iexp.upper = {
  //     parent,
  //     syn: None,
  //     interval,
  //     middle: new_middle,
  //     in_queue_upper: InQueue.default_upper(),
  //     deleted_upper: false,
  //   };
  //   splice(new_lower, new_upper);
  //   let update_list = [
  //     Update.NewAna(parent),
  //     Update.NewSyn(e),
  //     Update.NewAna(Lower(new_lower)),
  //     Update.NewSyn(new_upper),
  //   ];
  //   UpdateQueue.update_push_list(update_list, q);
  //   return_cursor(CursorExp(new_upper));
  // | (CursorExp(e), WrapAsc) =>
  //   let new_lower: Iexp.lower = {
  //     upper: dummy_upper(),
  //     ana: Some(Hole),
  //     marked: Unmarked,
  //     child: e,
  //     in_queue_lower: InQueue.default_lower(),
  //     deleted_lower: false,
  //   };
  //   let new_mid: Iexp.middle = Asc(new_lower, ref(Htyp.Hole));
  //   let new_upper: Iexp.upper = {
  //     parent: e.parent,
  //     syn: Some(Hole),
  //     interval: interval_around(e),
  //     middle: new_mid,
  //     in_queue_upper: InQueue.default_upper(),
  //     deleted_upper: false,
  //   };
  //   splice(new_lower, new_upper);
  //   let update_list = [
  //     Update.NewAna(new_upper.parent),
  //     Update.NewSyn(new_upper),
  //     Update.NewAna(Lower(new_lower)),
  //   ];
  //   UpdateQueue.update_push_list(update_list, q);
  //   return_cursor(CursorExp(new_upper));
  // | (CursorExp(e), Unwrap(child)) =>
  //   switch (e.middle) {
  //   | EHole => no_movement
  //   | Var(_, _, _)
  //   | NumLit(_)
  //   | Nil
  //   | Cons
  //   | ListRec(_)
  //   | ITE(_)
  //   | Y(_) => apply_action(state, Delete)
  //   | Lam(bind, _, _, _, body_lower, bound_vars) =>
  //     let body = body_lower.child;
  //     let parent = e.parent;
  //     let bound_var_set = bound_vars.contents;
  //     e.deleted_upper = true;
  //     body_lower.deleted_lower = true;
  //     replace(e, body);
  //     // update bound variables to outer binder
  //     switch (bind.contents) {
  //     | Hole => ()
  //     | Var(x) =>
  //       remove_from_binder_set(x, e, binder_set);
  //       let (new_binder, t, m) = look_up_binder(x, e, binder_set, root);
  //       add_bound_var_set(x, bound_var_set, new_binder);
  //       let update = var => update_var(var, t, m, new_binder);
  //       Tree.iter(update, bound_var_set);
  //     };
  //     // because updating vars could have deleted the body
  //     let new_body = child_of_parent(parent);
  //     // todo: maybe this could be a stream so that we don't have to wast time
  //     // appending sublists
  //     let bound_vars_list = Tree.list_of_t(bound_var_set);
  //     let update_list =
  //       [Update.NewAna(parent)]
  //       @ List.map(e => Update.NewSyn(e), bound_vars_list)
  //       @ [Update.NewSyn(new_body)];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(new_body));
  //   | Ap(fun_lower, _, arg_lower) =>
  //     let (body_lower, deleted_lower) =
  //       switch (child) {
  //       | One => (fun_lower, arg_lower)
  //       | Two => (arg_lower, fun_lower)
  //       | Three => raise(Unimplemented)
  //       };
  //     let body = body_lower.child;
  //     e.deleted_upper = true;
  //     body_lower.deleted_lower = true;
  //     delete_lower(deleted_lower);
  //     replace(e, body);
  //     let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(body));
  //   | Plus(left_arg, right_arg)
  //   | Pair(left_arg, right_arg, _) =>
  //     let (body_lower, deleted_lower) =
  //       switch (child) {
  //       | One => (left_arg, right_arg)
  //       | Two => (right_arg, left_arg)
  //       | Three => raise(Unimplemented)
  //       };
  //     let body = body_lower.child;
  //     e.deleted_upper = true;
  //     body_lower.deleted_lower = true;
  //     delete_lower(deleted_lower);
  //     replace(e, body);
  //     let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(body));
  //   | Proj(_, body_lower, _)
  //   | Asc(body_lower, _) =>
  //     let body = body_lower.child;
  //     e.deleted_upper = true;
  //     body_lower.deleted_lower = true;
  //     replace(e, body);
  //     let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
  //     UpdateQueue.update_push_list(update_list, q);
  //     return_cursor(CursorExp(body));
  //   }
  // };
};

let apply_actions = (actions: list(Action.t), s): Istate.t => {
  List.fold_left(apply_action, s, actions);
};
