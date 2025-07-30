open Sexplib.Std;
open Hazelnut;
open Order;
open Tree;
open Incremental;
open State;
open UpdateQueue;

// open Monad_lib.Monad;

let _string_of_interval = (i: (Order.t, Order.t)) =>
  "("
  ++ string_of_sexp(Order.sexp_of_t(fst(i)))
  ++ " , "
  ++ string_of_sexp(Order.sexp_of_t(snd(i)))
  ++ ")";

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two
    | Three;
};

module Iaction = {
  [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(Child.t)
    | Delete
    | WrapArrow(Child.t)
    | InsertNumType
    | InsertBoolType
    | InsertUnitType
    | InsertLt
    | InsertITE
    | InsertList
    | InsertNumLit(int)
    | InsertVar(string)
    | InsertNil
    | InsertCons
    | InsertListRec
    | InsertListMatch
    | InsertY
    | InsertTypVar(string)
    | WrapPlus(Child.t)
    | WrapAp(Child.t)
    | WrapPair(Child.t)
    | WrapProduct(Child.t)
    | WrapProj(ProdSide.t)
    | WrapLam
    | WrapAsc
    | WrapTypAp
    | WrapTypFun
    | WrapForAll
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

let set_child_in_parent = (p: Iexp.parent, c: Iexp.upper): unit => {
  switch (p) {
  | Deleted => ()
  | Root(r) => r.root_child = c
  | Lower(r) => r.child = c
  };
};

let replace = (e: Iexp.upper, e': Iexp.upper): unit => {
  e'.parent = e.parent;
  set_child_in_parent(e.parent, e');
  e.parent = Deleted;
};

let splice = (new_lower: Iexp.lower, new_upper: Iexp.upper): unit => {
  new_lower.upper = new_upper; //skip up
  set_child_in_parent(new_upper.parent, new_upper); //fix parent
  new_lower.child.parent = Lower(new_lower); //fix child
};

let upper_of_parent = (p: Iexp.parent): option(Iexp.upper) => {
  switch (p) {
  | Deleted
  | Root(_) => None
  | Lower(r) => Some(r.upper)
  };
};

// Given either the root or a lower contained
// in a binder, returns the set of variable expressions
// bound to that binder.
//
// Side effect: if the root is provided
// to this function, and the variable is not
// in the free set, then it will be added to the free set.
let var_set_of_binder =
    (x: (string, BinderKind.t)): (Iexp.parent => Iexp.var_set) =>
  fun
  | Deleted => failwith("var set of deleted root")
  | Root(root) => {
      switch (Hashtbl.find_opt(root.free_vars, x)) {
      | None =>
        let new_set = ref(Tree.empty);
        Hashtbl.add(root.free_vars, x, new_set);
        new_set;
      | Some(var_set) => var_set
      };
    }
  | Lower(lower) =>
    switch (lower.upper.middle) {
    | Lam(_, _, _, _, _, bound_vars, _)
    | TypFun(_, _, _, bound_vars) => bound_vars
    | _ => failwith("non-lam binder")
    };

let name_of_var_upper = (e: Iexp.upper): string =>
  switch (e.middle) {
  | Var(x, _, _) => x
  | _ => failwith("name_of_var_upper called on non-var")
  };

// Remove expression variable from provided lower contained in
// a binder, or from the root free vars.
let unbind_from_binder_var = (var: Iexp.upper, parent: Iexp.parent) => {
  Iexp.remove_bound_var(
    var,
    var_set_of_binder((name_of_var_upper(var), Lam), parent),
  );
};

// Adds expression variable from provided lower contained in
// a binder, or to the root free vars.
let bind_to_binder_var = (var: Iexp.upper, parent: Iexp.parent) => {
  // print_endline("adding to binder");
  Iexp.add_bound_var(
    var,
    var_set_of_binder((name_of_var_upper(var), Lam), parent),
    // print_endline(
    //   "now has this many: "
    //   ++ string_of_int(
    //        List.length(
    //          Tree.list_of_t(
    //            var_set_of_binder(name_of_var_upper(var), parent).contents,
    //          ),
    //        ),
    //      ),
    // );
  );
};

// Removes the expression containing some type variable from
// the provided binder's variable set, or from the root free vars.
// It is removed from the entry corresponding to the type variable's
// name.
let unbind_from_binder_typ =
    (containing_upper: Iexp.upper, name: string, binders_parent: Iexp.parent) => {
  Iexp.remove_bound_var(
    containing_upper,
    var_set_of_binder((name, TypFun), binders_parent),
  );
};

// Adds the expression containing some type variable to
// the provided binder's variable set, or to the root free vars.
// It is put under the entry corresponding to the type variable's
// name.
let bind_to_binder_typ =
    (containing_upper: Iexp.upper, name: string, binders_parent: Iexp.parent) => {
  Iexp.add_bound_var(
    containing_upper,
    var_set_of_binder((name, TypFun), binders_parent),
  );
};

// precondition: e.middle is a Var
// makes [e] synthesize [syn], marks [e] as [m], and updates their
// binding on both ends. It also marks them as on the update queue with new syn.
let update_var =
    (e: Iexp.upper, syn: Htyp.t, new_mark: Mark.t, new_binder: Iexp.binder)
    : unit => {
  switch (e.middle) {
  | Var(_, mark, binder) =>
    // remove this var from its previous binder
    unbind_from_binder_var(e, binder.contents);
    // set the local binder, mark, and syn type
    binder.contents = new_binder;
    mark.contents = new_mark;
    e.syn = Some(syn);
  | _ => failwith("update_var called on non-var")
  };
};

// Finds the looks up [name] in the context of [e].
// Side effect: splaying
// Returns:
// - the binding site (or root)
// - if the binding site is a lambda, then the annotated type
// - whether the variable is free
let look_up_binder =
    (
      x: (string, BinderKind.t),
      e: Iexp.upper,
      binder_set: BinderSet.t,
      root: Iexp.root,
    )
    : (Iexp.parent, Htyp.t, Mark.t) => {
  let free: (Iexp.parent, Htyp.t, Mark.t) = (Root(root), Hole, Marked);
  switch (Hashtbl.find_opt(binder_set, x)) {
  | None => free
  | Some(x_binder_set) =>
    switch (Tree.splay_tightest(e.interval, x_binder_set)) {
    | None => free
    | Some((upper, splayed)) =>
      Hashtbl.replace(binder_set, x, splayed);
      let (name, binder_kind) = x;
      switch (upper.entry.middle) {
      | Lam(bind, t, _, _, body, _, _)
          when Bind.Var(name) == bind.contents && binder_kind == Lam => (
          Lower(body),
          t.contents,
          Unmarked,
        )
      | TypFun(bind, _, body, _)
          when Bind.Var(name) == bind.contents && binder_kind == TypFun => (
          Lower(body),
          Hole,
          Unmarked,
        )
      | _ => failwith("invalid binder lookup")
      };
    }
  };
};

// Dumb version of look_up_binder for comparison
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

let add_bound_var_set =
    (
      x: (string, BinderKind.t),
      joining_set: Tree.t(Iexp.upper),
      binder: Iexp.parent,
    ) => {
  let parent_var_set = var_set_of_binder(x, binder);
  Iexp.union_bound_vars(joining_set, parent_var_set);
};

let capture_name =
    (
      x: (string, BinderKind.t),
      e: Iexp.upper,
      binder_set: BinderSet.t,
      root: Iexp.root,
    ) => {
  let (ancestor_binder, _, _) = look_up_binder(x, e, binder_set, root);
  // print_endline("capturing name: " ++ x);
  // switch (ancestor_binder) {
  // | Root(_) => print_endline("it was free before")
  // | _ => print_endline("it was bound before")
  // };
  let found_vars = var_set_of_binder(x, ancestor_binder);
  // print_endline(
  //   "this many in parental scope: "
  //   ++ string_of_int(List.length(Tree.list_of_t(found_vars.contents))),
  // );
  // let intervals =
  //   List.map(
  //     (upper: Iexp.upper) => string_of_interval(upper.interval),
  //     Tree.list_of_t(found_vars.contents),
  //   );
  // print_endline("parent var intervals: " ++ String.concat(", ", intervals));
  // print_endline("excising interval: " ++ string_of_interval(e.interval));
  let excised_vars = Iexp.excise_bound_vars(e.interval, found_vars);
  // print_endline(
  //   "this many excised: "
  //   ++ string_of_int(List.length(Tree.list_of_t(excised_vars))),
  // );
  // print_endline(
  //   "now this many in parental scope: "
  //   ++ string_of_int(List.length(Tree.list_of_t(found_vars.contents))),
  // );
  excised_vars;
};

// Dumb version of capture_name for comparison
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

let remove_from_binder_set =
    (x: (string, BinderKind.t), e: Iexp.upper, binder_set: BinderSet.t) => {
  switch (Hashtbl.find_opt(binder_set, x)) {
  | None => failwith("removing binder that doesn't exist")
  | Some(var_set) =>
    let new_set = Tree.delete(fst(e.interval), var_set);
    if (Tree.is_empty(new_set)) {
      Hashtbl.remove(binder_set, x);
    } else {
      Hashtbl.replace(binder_set, x, new_set);
    };
  };
};

let add_to_binder_set =
    (x: (string, BinderKind.t), e: Iexp.upper, binder_set: BinderSet.t) => {
  // print_endline("adding binder at: " ++ _string_of_interval(e.interval));
  switch (Hashtbl.find_opt(binder_set, x)) {
  | None =>
    let new_set =
      Tree.insert(e, fst(e.interval), snd(e.interval), Tree.empty);
    Hashtbl.add(binder_set, x, new_set);
  | Some(x_binder_set) =>
    let new_x_binder_set =
      Tree.insert(e, fst(e.interval), snd(e.interval), x_binder_set);
    Hashtbl.replace(binder_set, x, new_x_binder_set);
  };
};

let rec delete_lower = (e: Iexp.lower) => {
  e.deleted_lower = true;
  delete_upper(e.child);
}

and delete_middle = (e: Iexp.middle, upper: Iexp.upper) => {
  switch (e) {
  | EHole
  | NumLit(_)
  | Nil
  | Cons
  | ITE(_)
  | ListRec(_) => ()
  | Y(_) => ()
  | Var(x, _, binder) =>
    let var_set = var_set_of_binder((x, BinderKind.Lam), binder.contents);
    Iexp.remove_bound_var(upper, var_set);
  | Asc(e, _, _) => delete_lower(e)
  | Lam(_, _, _, _, e, _, _)
  | TypFun(_, _, e, _) => delete_lower(e)
  | Plus(e1, e2) =>
    delete_lower(e1);
    delete_lower(e2);
  | Ap(e1, _, e2) =>
    delete_lower(e1);
    delete_lower(e2);
  | TypAp(e, _, _, _) => delete_lower(e)
  | Pair(e1, e2, _) =>
    delete_lower(e1);
    delete_lower(e2);
  | Proj(_, e, _) => delete_lower(e)
  };
}

and delete_upper = (e: Iexp.upper) => {
  e.deleted_upper = true;
  delete_middle(e.middle, e);
};

let interval_around = (e: Iexp.upper) => {
  let (b, c) = e.interval;
  let a = Order.add_prev(b);
  let d = Order.add_next(c);
  // a < b < c < d
  assert(Order.lt(a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, d));
  (a, d);
};

let interval_after = (e: Iexp.upper) => {
  let (_a, b) = e.interval;
  let c = Order.add_next(b);
  let d = Order.add_next(c);
  // a < b < c < d
  assert(Order.lt(_a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, d));
  (c, d);
};

let interval_before = (e: Iexp.upper) => {
  let (c, _d) = e.interval;
  let b = Order.add_prev(c);
  let a = Order.add_prev(b);
  // a < b < c < d
  assert(Order.lt(a, b));
  assert(Order.lt(b, c));
  assert(Order.lt(c, _d));
  (a, b);
};

module TypVarSet = Set.Make(String);

// Returns the provided type, but with all type variables bound
// to alpha changed their mark. Doesn't go past shadowing.
let rec htyp_update_mark =
        (t: Htyp.t, alpha: string, new_mark: Mark.t): Htyp.t => {
  switch (t) {
  | TypVar(beta, _) =>
    switch (beta) {
    | Hole => t
    | Var(beta) =>
      if (beta == alpha) {
        TypVar(Var(alpha), new_mark);
      } else {
        t;
      }
    }
  | ForAll(beta, tbody) =>
    ForAll(beta, htyp_update_mark(tbody, alpha, new_mark))
  | Arrow(tin, tout) =>
    Arrow(
      htyp_update_mark(tin, alpha, new_mark),
      htyp_update_mark(tout, alpha, new_mark),
    )
  | Product(t1, t2) =>
    Product(
      htyp_update_mark(t1, alpha, new_mark),
      htyp_update_mark(t2, alpha, new_mark),
    )
  | _ => t
  };
};

let rec ztyp_update_mark =
        (z: Ztyp.t, alpha: string, new_mark: Mark.t): Ztyp.t => {
  switch (z) {
  | Cursor(t) => Cursor(htyp_update_mark(t, alpha, new_mark))
  | LArrow(z, t) =>
    LArrow(
      ztyp_update_mark(z, alpha, new_mark),
      htyp_update_mark(t, alpha, new_mark),
    )
  | RArrow(t, z) =>
    RArrow(
      htyp_update_mark(t, alpha, new_mark),
      ztyp_update_mark(z, alpha, new_mark),
    )
  | LProduct(z, t) =>
    LProduct(
      ztyp_update_mark(z, alpha, new_mark),
      htyp_update_mark(t, alpha, new_mark),
    )
  | RProduct(t, z) =>
    RProduct(
      htyp_update_mark(t, alpha, new_mark),
      ztyp_update_mark(z, alpha, new_mark),
    )
  | ForAll(Bind.Var(beta), _) when alpha == beta => z
  | ForAllCursorBind(Bind.Var(beta), _) when alpha == beta => z
  | ForAll(other, z) => ForAll(other, ztyp_update_mark(z, alpha, new_mark))
  | ForAllCursorBind(other, t) =>
    ForAllCursorBind(other, htyp_update_mark(t, alpha, new_mark))
  };
};

// Collects the names of all marked type variables in the input Htyp.
let rec htyp_collect_marked: Htyp.t => TypVarSet.t =
  fun
  | TypVar(Var(alpha), Marked) => TypVarSet.singleton(alpha)
  | ForAll(_, t) => htyp_collect_marked(t)
  | Arrow(tin, tout) =>
    TypVarSet.union(htyp_collect_marked(tin), htyp_collect_marked(tout))
  | Product(t1, t2) =>
    TypVarSet.union(htyp_collect_marked(t1), htyp_collect_marked(t2))
  | _ => TypVarSet.empty;

// Collects the names of all marked type variables in the input Ztyp.
let rec ztyp_collect_marked: Ztyp.t => TypVarSet.t =
  fun
  | Cursor(t) => htyp_collect_marked(t)
  | LArrow(z, t) =>
    TypVarSet.union(ztyp_collect_marked(z), htyp_collect_marked(t))
  | RArrow(t, z) =>
    TypVarSet.union(htyp_collect_marked(t), ztyp_collect_marked(z))
  | LProduct(z, t) =>
    TypVarSet.union(ztyp_collect_marked(z), htyp_collect_marked(t))
  | RProduct(t, z) =>
    TypVarSet.union(htyp_collect_marked(t), ztyp_collect_marked(z))
  | ForAll(_, z) => ztyp_collect_marked(z)
  | ForAllCursorBind(_, t) => htyp_collect_marked(t);

// Applies an action to a Ztyp, assuming nothing about the
// context of type variable binders in outer expressions
// containing this Ztyp.
// Additionally returns a boolean for whether
// any type variable changes occurred that could affect outside
// binder-boundvar pointers.
let rec apply_action_typ_local =
        (local_ctx: TypVarSet.t, z: Ztyp.t, a: Iaction.t): (Ztyp.t, bool) => {
  let typvars_affected = ref(false);
  let z_after_action =
    switch (z, a) {
    // Significant MoveUp cases
    | (Cursor(_), MoveUp) => z
    | (LArrow(Cursor(t1), t2), MoveUp)
    | (RArrow(t1, Cursor(t2)), MoveUp) => Cursor(Arrow(t1, t2))
    | (LProduct(Cursor(t1), t2), MoveUp)
    | (RProduct(t1, Cursor(t2)), MoveUp) => Cursor(Product(t1, t2))
    | (ForAll(name, Cursor(body_t)), MoveUp)
    | (ForAllCursorBind(name, body_t), MoveUp) =>
      Cursor(ForAll(name, body_t))
    | (Cursor(Hole), MoveDown(_))
    | (Cursor(Num), MoveDown(_))
    | (Cursor(Bool), MoveDown(_))
    | (Cursor(Unit), MoveDown(_))
    | (Cursor(List), MoveDown(_))
    | (Cursor(TypVar(_)), MoveDown(_))
    | (ForAllCursorBind(_), MoveDown(_)) => z
    | (Cursor(Arrow(t1, t2)), MoveDown(One)) => LArrow(Cursor(t1), t2)
    | (Cursor(Arrow(t1, t2)), MoveDown(Two)) => RArrow(t1, Cursor(t2))
    | (Cursor(Arrow(_)), MoveDown(Three)) => z
    | (Cursor(Product(t1, t2)), MoveDown(One)) => LProduct(Cursor(t1), t2)
    | (Cursor(Product(t1, t2)), MoveDown(Two)) => RProduct(t1, Cursor(t2))
    | (Cursor(Product(_)), MoveDown(Three)) => z
    | (Cursor(ForAll(alpha, t)), MoveDown(_)) => ForAll(alpha, Cursor(t))
    | (Cursor(_), Delete) => Cursor(Hole)
    | (Cursor(Hole), InsertNumType) => Cursor(Num)
    | (Cursor(Hole), InsertBoolType) => Cursor(Bool)
    | (Cursor(Hole), InsertUnitType) => Cursor(Unit)
    | (Cursor(Hole), InsertList) => Cursor(List)
    | (Cursor(Hole), InsertTypVar(alpha)) =>
      typvars_affected := true;
      Cursor(
        TypVar(
          Bind.Var(alpha),
          TypVarSet.mem(alpha, local_ctx) ? Unmarked : Marked,
        ),
      );
    | (Cursor(t), WrapForAll) => Cursor(ForAll(Bind.Hole, t))
    | (Cursor(_), InsertNumType)
    | (Cursor(_), InsertBoolType)
    | (Cursor(_), InsertUnitType)
    | (Cursor(_), InsertList)
    | (Cursor(_), InsertTypVar(_)) => z
    | (Cursor(t), WrapArrow(One)) => Cursor(Arrow(t, Hole))
    | (Cursor(t), WrapArrow(Two)) => Cursor(Arrow(Hole, t))
    | (Cursor(_), WrapArrow(Three)) => z
    | (Cursor(t), WrapProduct(One)) => Cursor(Product(t, Hole))
    | (Cursor(t), WrapProduct(Two)) => Cursor(Product(Hole, t))
    | (Cursor(_), WrapProduct(Three)) => z
    | (Cursor(Hole), Unwrap(_)) => z
    | (Cursor(Num), Unwrap(_)) => z
    | (Cursor(Bool), Unwrap(_)) => z
    | (Cursor(Unit), Unwrap(_)) => z
    | (Cursor(List), Unwrap(_)) => z
    | (Cursor(TypVar(_, _)), Unwrap(_)) => z
    | (Cursor(Arrow(t, _)), Unwrap(One))
    | (Cursor(Arrow(_, t)), Unwrap(Two)) => Cursor(t)
    | (Cursor(Arrow(_)), Unwrap(Three)) => z
    | (Cursor(Product(t, _)), Unwrap(One))
    | (Cursor(Product(_, t)), Unwrap(Two)) => Cursor(t)
    | (Cursor(Product(_)), Unwrap(Three)) => z
    | (Cursor(ForAll(Bind.Hole, t)), Unwrap(_)) => Cursor(t)
    | (Cursor(ForAll(Bind.Var(alpha), t)), Unwrap(_)) =>
      typvars_affected := true;
      Cursor(
        TypVarSet.mem(alpha, local_ctx)
          ? t : htyp_update_mark(t, alpha, Marked),
      );
    | (ForAllCursorBind(Bind.Hole, t), InsertTypVar(alpha)) =>
      typvars_affected := true;
      ForAllCursorBind(
        Bind.Var(alpha),
        TypVarSet.mem(alpha, local_ctx)
          ? t : htyp_update_mark(t, alpha, Unmarked),
      );
    | (ForAllCursorBind(Bind.Var(alpha), t), Delete) =>
      typvars_affected := true;
      ForAllCursorBind(
        Bind.Hole,
        TypVarSet.mem(alpha, local_ctx)
          ? t : htyp_update_mark(t, alpha, Marked),
      );
    // Any action that isn't insert type variable, delete, or move up
    // does nothing on a ForAllCursorBind.
    | (ForAllCursorBind(_), InsertNumType)
    | (ForAllCursorBind(_), InsertBoolType)
    | (ForAllCursorBind(_), InsertUnitType)
    | (ForAllCursorBind(_), InsertList)
    | (ForAllCursorBind(_), WrapArrow(_))
    | (ForAllCursorBind(_), WrapProduct(_))
    | (ForAllCursorBind(_), Unwrap(_))
    | (ForAllCursorBind(_), WrapForAll)
    // Also, attempting to insert type variable to a binder
    // that already has one does nothing.
    | (ForAllCursorBind(Bind.Var(_), _), InsertTypVar(_))
    // Likewise deleting the type variable in a binder
    // that already is a hole does nothing.
    | (ForAllCursorBind(Bind.Hole, _), Delete) => z
    | (LArrow(z, t), MoveUp)
    | (LArrow(z, t), MoveDown(_))
    | (LArrow(z, t), Delete)
    | (LArrow(z, t), InsertNumType)
    | (LArrow(z, t), InsertBoolType)
    | (LArrow(z, t), InsertUnitType)
    | (LArrow(z, t), InsertList)
    | (LArrow(z, t), WrapArrow(_))
    | (LArrow(z, t), WrapProduct(_))
    | (LArrow(z, t), Unwrap(_))
    | (LArrow(z, t), WrapForAll)
    | (LArrow(z, t), InsertTypVar(_)) =>
      let (sub_z, sub_typvars_affected) =
        apply_action_typ_local(local_ctx, z, a);
      typvars_affected := sub_typvars_affected;
      LArrow(sub_z, t);
    | (RArrow(t, z), MoveUp)
    | (RArrow(t, z), MoveDown(_))
    | (RArrow(t, z), Delete)
    | (RArrow(t, z), InsertNumType)
    | (RArrow(t, z), InsertBoolType)
    | (RArrow(t, z), InsertUnitType)
    | (RArrow(t, z), InsertList)
    | (RArrow(t, z), WrapArrow(_))
    | (RArrow(t, z), WrapProduct(_))
    | (RArrow(t, z), Unwrap(_))
    | (RArrow(t, z), WrapForAll)
    | (RArrow(t, z), InsertTypVar(_)) =>
      let (sub_z, sub_typvars_affected) =
        apply_action_typ_local(local_ctx, z, a);
      typvars_affected := sub_typvars_affected;
      RArrow(t, sub_z);
    | (LProduct(z, t), MoveUp)
    | (LProduct(z, t), MoveDown(_))
    | (LProduct(z, t), Delete)
    | (LProduct(z, t), InsertNumType)
    | (LProduct(z, t), InsertBoolType)
    | (LProduct(z, t), InsertUnitType)
    | (LProduct(z, t), InsertList)
    | (LProduct(z, t), WrapArrow(_))
    | (LProduct(z, t), WrapProduct(_))
    | (LProduct(z, t), Unwrap(_))
    | (LProduct(z, t), WrapForAll)
    | (LProduct(z, t), InsertTypVar(_)) =>
      let (sub_z, sub_typvars_affected) =
        apply_action_typ_local(local_ctx, z, a);
      typvars_affected := sub_typvars_affected;
      LProduct(sub_z, t);
    | (RProduct(t, z), MoveUp)
    | (RProduct(t, z), MoveDown(_))
    | (RProduct(t, z), Delete)
    | (RProduct(t, z), InsertNumType)
    | (RProduct(t, z), InsertBoolType)
    | (RProduct(t, z), InsertUnitType)
    | (RProduct(t, z), InsertList)
    | (RProduct(t, z), WrapArrow(_))
    | (RProduct(t, z), WrapProduct(_))
    | (RProduct(t, z), Unwrap(_))
    | (RProduct(t, z), WrapForAll)
    | (RProduct(t, z), InsertTypVar(_)) =>
      let (sub_z, sub_typvars_affected) =
        apply_action_typ_local(local_ctx, z, a);
      typvars_affected := sub_typvars_affected;
      RProduct(t, sub_z);
    | (ForAll(alpha, z), MoveUp)
    | (ForAll(alpha, z), MoveDown(_))
    | (ForAll(alpha, z), Delete)
    | (ForAll(alpha, z), InsertNumType)
    | (ForAll(alpha, z), InsertBoolType)
    | (ForAll(alpha, z), InsertUnitType)
    | (ForAll(alpha, z), InsertList)
    | (ForAll(alpha, z), WrapArrow(_))
    | (ForAll(alpha, z), WrapProduct(_))
    | (ForAll(alpha, z), Unwrap(_))
    | (ForAll(alpha, z), WrapForAll)
    | (ForAll(alpha, z), InsertTypVar(_)) =>
      let new_ctx =
        switch (alpha) {
        | Var(alpha) => TypVarSet.add(alpha, local_ctx)
        | Hole => local_ctx
        };
      let (sub_z, sub_typvars_affected) =
        apply_action_typ_local(new_ctx, z, a);
      typvars_affected := sub_typvars_affected;
      ForAll(alpha, sub_z);
    | (z, WrapAsc) => z
    | (z, InsertNumLit(_)) => z
    | (z, InsertVar(_)) => z
    | (z, InsertNil) => z
    | (z, InsertCons) => z
    | (z, InsertListRec) => z
    | (z, InsertListMatch) => z
    | (z, InsertY) => z
    | (z, InsertLt) => z
    | (z, InsertITE) => z
    | (z, WrapPlus(_)) => z
    | (z, WrapAp(_)) => z
    | (z, WrapPair(_)) => z
    | (z, WrapProj(_)) => z
    | (z, WrapLam) => z
    | (z, WrapTypFun) => z
    | (z, WrapTypAp) => z
    };
  (z_after_action, typvars_affected^);
};

// I feel like this could totally be incrementalized more granularly.
// z after action is locally accurate, but some unmarked stuff may
// actually be bound.
let fixup_pointers =
    (
      z_after_action: Ztyp.t,
      containing_upper: Iexp.upper,
      root: Iexp.root,
      binder_set: BinderSet.t,
    )
    : Ztyp.t => {
  let escaped_typ_vars = ztyp_collect_marked(z_after_action);
  let typ_binders =
    switch (containing_upper.middle) {
    | Lam(_, _, _, _, _, _, typ_binders)
    | Asc(_, _, typ_binders)
    | ListRec(_, typ_binders)
    | Y(_, typ_binders)
    | ITE(_, typ_binders)
    | TypAp(_, _, _, typ_binders) => typ_binders
    | _ =>
      failwith(
        "[fixup_pointers] Type action application happened in containing_upper",
      )
    };

  let result = ref(z_after_action);

  // Remove typvars that are now entirely locally contained
  let unbind = (alpha: string, binder_parent: Iexp.parent) => {
    unbind_from_binder_typ(containing_upper, alpha, binder_parent);
  };

  Hashtbl.iter(unbind, Hashtbl.copy(typ_binders));
  Hashtbl.filter_map_inplace(
    (alpha, binder_parent) => {
      TypVarSet.mem(alpha, escaped_typ_vars) ? Some(binder_parent) : None
    },
    typ_binders,
  );

  // Add typvars that are unbound, also update the type to reflect
  // the new bound status
  let add_escaped = (alpha: string) =>
    if (!Hashtbl.mem(typ_binders, alpha)) {
      let (binder_parent, _, mark) =
        look_up_binder((alpha, TypFun), containing_upper, binder_set, root);
      bind_to_binder_typ(containing_upper, alpha, binder_parent);
      Hashtbl.replace(typ_binders, alpha, binder_parent);
      result := ztyp_update_mark(result^, alpha, mark);
    };
  TypVarSet.iter(add_escaped, escaped_typ_vars);

  result^;
};

let apply_action_typ =
    (
      containing_upper: Iexp.upper,
      z: Ztyp.t,
      a: Iaction.t,
      root: Iexp.root,
      binder_set: BinderSet.t,
    )
    : Ztyp.t => {
  let (local_z, typvar_affected) =
    apply_action_typ_local(TypVarSet.empty, z, a);
  if (typvar_affected) {
    fixup_pointers(local_z, containing_upper, root, binder_set);
  } else {
    local_z;
  };
};

// Extracts the new-type update variant from the upper's middle.
let typ_update_of_upper = (containing_upper: Iexp.upper): Update.t => {
  switch (containing_upper.middle) {
  | Lam(_) => NewAnn(containing_upper)
  | Asc(_) => NewAsc(containing_upper)
  | ListRec(_) => NewListRec(containing_upper)
  | Y(_) => NewY(containing_upper)
  | ITE(_) => NewITE(containing_upper)
  | TypAp(_) => NewTypAp(containing_upper)
  | _ =>
    failwith(
      "Tried to get new-type update variant from an upper with no type.",
    )
  };
};

let typ_binders_of_upper = (containing_upper: Iexp.upper): Iexp.typ_binders => {
  switch (containing_upper.middle) {
  | Lam(_, _, _, _, _, _, typ_binders)
  | Asc(_, _, typ_binders)
  | ListRec(_, typ_binders)
  | Y(_, typ_binders)
  | ITE(_, typ_binders)
  | TypAp(_, _, _, typ_binders) => typ_binders
  | _ => failwith("Tried to get typ_binders from an upper with no type.")
  };
};

let typ_ref_of_upper = (containing_upper: Iexp.upper): ref(Htyp.t) => {
  switch (containing_upper.middle) {
  | Lam(_, t, _, _, _, _, _)
  | Asc(_, t, _)
  | ListRec(t, _)
  | Y(t, _)
  | ITE(t, _)
  | TypAp(_, _, t, _) => t
  | _ => failwith("Tried to get type from an upper with no type.")
  };
};

// these belong in Pexp, copied for convenience

let _string_of_child: Child.t => string =
  fun
  | One => "One"
  | Two => "Two"
  | Three => "Three";

let _string_of_prod_side: ProdSide.t => string =
  fun
  | Fst => "fst"
  | Snd => "snd";

let _string_of_action: Iaction.t => string =
  fun
  | MoveUp => "MoveUp"
  | MoveDown(c) => "MoveDown(" ++ _string_of_child(c) ++ ")"
  | Delete => "Delete"
  | WrapArrow(c) => "WrapArrow(" ++ _string_of_child(c) ++ ")"
  | InsertNumType => "InsertNumType"
  | InsertBoolType => "InsertBoolType"
  | InsertUnitType => "InsertUnitType"
  | InsertList => "InserList"
  | InsertNil => "InsertNil"
  | InsertCons => "InsertCons"
  | InsertListRec => "InsertListRec"
  | InsertListMatch => "InsertListMatch"
  | InsertY => "InsertY"
  | InsertLt => "InsertLt"
  | InsertITE => "InsertITE"
  | InsertNumLit(x) => "InsertNumLit(" ++ string_of_int(x) ++ ")"
  | InsertVar(s) => "InsertVar(\"" ++ s ++ "\")"
  | WrapPlus(c) => "WrapPlus(" ++ _string_of_child(c) ++ ")"
  | WrapAp(c) => "WrapAp(" ++ _string_of_child(c) ++ ")"
  | WrapPair(c) => "WrapPair(" ++ _string_of_child(c) ++ ")"
  | WrapProduct(c) => "WrapProduct(" ++ _string_of_child(c) ++ ")"
  | WrapProj(prod_side) =>
    "WrapProj(" ++ _string_of_prod_side(prod_side) ++ ")"
  | WrapLam => "WrapLam"
  | WrapAsc => "WrapAsc"
  | WrapTypAp => "WrapTypAp"
  | WrapTypFun => "WrapTypFun"
  | WrapForAll => "WrapForAll"
  | InsertTypVar(s) => "InsertTypVar(\"" ++ s ++ "\")"
  | Unwrap(c) => "Unwrap(" ++ _string_of_child(c) ++ ")";

let rec apply_action = (state: Istate.t, a: Iaction.t): Istate.t => {
  let root = state.ephemeral.root;
  let q = state.ephemeral.q;
  let binder_set = state.ephemeral.binder_set;
  let c = state.persistent.c;
  let no_movement: Istate.t = state;

  // print_endline("ACT: " ++ _string_of_action(a));

  let return_cursor = (c: Icursor.t): Istate.t => {
    ephemeral: state.ephemeral,
    persistent: {
      c: c,
    },
  };

  switch (c, a) {
  | (CursorBind(e), MoveUp) => return_cursor(CursorExp(e))
  | (CursorBind(e), Delete) =>
    switch (e.middle) {
    | Lam(bind, _t, _m1, _m2, body, bound_vars, _) =>
      switch (bind.contents) {
      | Var(x) =>
        bind.contents = Hole;
        remove_from_binder_set((x, BinderKind.Lam), e, binder_set);
        let bound_var_set = bound_vars.contents;

        let (new_binder, t, m) =
          look_up_binder((x, BinderKind.Lam), e, binder_set, root);

        add_bound_var_set((x, BinderKind.Lam), bound_var_set, new_binder);

        let update = var => update_var(var, t, m, new_binder);
        Tree.iter(update, bound_var_set);

        let bound_var_list = Tree.list_of_t(bound_var_set);
        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => Update.NewSyn(e), bound_var_list)
          @ [NewAna(Lower(body)), NewSyn(body.child)];
        UpdateQueue.update_push_list(update_list, q);
        no_movement;
      | Hole => no_movement
      }
    | TypFun(bind, _, body, bound_vars) =>
      switch (bind^) {
      | Var(x) =>
        bind.contents = Hole;

        remove_from_binder_set((x, BinderKind.TypFun), e, binder_set);

        // Binder -> Boundvars
        let (new_binder, _, m) =
          look_up_binder((x, BinderKind.TypFun), e, binder_set, root);
        add_bound_var_set((x, BinderKind.TypFun), bound_vars^, new_binder);

        // Boundvars -> Binder
        let update = (containing_upper: Iexp.upper) => {
          let t = typ_ref_of_upper(containing_upper);
          t := htyp_update_mark(t^, x, m);
          Hashtbl.replace(
            typ_binders_of_upper(containing_upper),
            x,
            new_binder,
          );
        };
        Tree.iter(update, bound_vars^);

        let bound_var_list = Tree.list_of_t(bound_vars^);
        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => Update.NewSyn(e), bound_var_list)
          @ [NewAna(Lower(body)), NewSyn(body.child)]; // TODO: Doublecheck this
        UpdateQueue.update_push_list(update_list, q);
        no_movement;
      | Hole => no_movement
      }
    | _ => failwith("CursorBind on non lambda and non typfun")
    }
  | (CursorBind(e), InsertVar(x)) =>
    switch (e.middle) {
    | Lam(bind, t, _m1, _m2, body, bound_vars, _) =>
      switch (bind.contents) {
      | Hole =>
        bind.contents = Var(x);
        add_to_binder_set((x, BinderKind.Lam), e, binder_set);

        bound_vars.contents =
          capture_name((x, BinderKind.Lam), e, binder_set, root);

        let update = var =>
          update_var(var, t.contents, Unmarked, Iexp.Lower(body));
        Tree.iter(update, bound_vars.contents);
        let newly_bound_list = Tree.list_of_t(bound_vars.contents);
        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => Update.NewSyn(e), newly_bound_list)
          @ [NewAna(Lower(body)), NewSyn(body.child)];
        UpdateQueue.update_push_list(update_list, q);
        no_movement;
      | Var(_) => no_movement
      }
    | TypFun(_) => no_movement
    | _ => failwith("CursorBind on non lambda/typfun")
    }
  | (CursorBind(e), InsertTypVar(x)) =>
    switch (e.middle) {
    | Lam(_) => no_movement
    | TypFun(bind, _, body, bound_vars) =>
      switch (bind^) {
      | Hole =>
        bind := Var(x);
        add_to_binder_set((x, BinderKind.TypFun), e, binder_set);

        // Look up to find old binder.
        // Binder -> Boundvars
        bound_vars :=
          capture_name((x, BinderKind.TypFun), e, binder_set, root);

        // Boundvars -> Binder
        let update = (containing_upper: Iexp.upper) => {
          let t = typ_ref_of_upper(containing_upper);
          t := htyp_update_mark(t^, x, Unmarked);
          Hashtbl.replace(
            typ_binders_of_upper(containing_upper),
            x,
            Iexp.Lower(body),
          );
        };
        Tree.iter(update, bound_vars^);

        // Updates
        let newly_bound_list = Tree.list_of_t(bound_vars^);
        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => typ_update_of_upper(e), newly_bound_list)
          @ [NewAna(Lower(body)), NewSyn(body.child)];
        UpdateQueue.update_push_list(update_list, q);

        no_movement;
      | Var(_) => no_movement
      }
    | _ => failwith("CursorBind on non lambda/typfun")
    }
  | (CursorBind(_), _) => no_movement
  | (CursorTyp(e, Cursor(_)), MoveUp) => return_cursor(CursorExp(e))
  | (CursorTyp(e, z), a) =>
    let t = typ_ref_of_upper(e);
    let z' = apply_action_typ(e, z, a, root, binder_set);
    let t' = erase_typ(z');
    t := t';
    UpdateQueue.update_push(typ_update_of_upper(e), q);
    return_cursor(CursorTyp(e, z'));
  | (CursorExp(e), MoveUp) =>
    switch (upper_of_parent(e.parent)) {
    | None => no_movement
    | Some(e') => return_cursor(CursorExp(e'))
    }
  | (CursorExp(e), MoveDown(child)) =>
    switch (e.middle) {
    | Var(_, _, _)
    | NumLit(_)
    | EHole
    | Nil
    | Cons => no_movement
    | Plus(e1, e2)
    | Pair(e1, e2, _)
    | Ap(e1, _, e2) =>
      switch (child) {
      | One => return_cursor(CursorExp(e1.child))
      | Two => return_cursor(CursorExp(e2.child))
      | Three => no_movement
      }
    | Lam(_, t, _, _, e1, _, _) =>
      switch (child) {
      | One => return_cursor(CursorBind(e))
      | Two => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Three => return_cursor(CursorExp(e1.child))
      }
    | Asc(e1, t, _) =>
      switch (child) {
      | One => return_cursor(CursorExp(e1.child))
      | Two => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Three => no_movement
      }
    | Proj(_, e, _) =>
      switch (child) {
      | One => return_cursor(CursorExp(e.child))
      | Two => no_movement
      | Three => no_movement
      }
    | ListRec(t, _) =>
      switch (child) {
      | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Two
      | Three => no_movement
      }
    | Y(t, _) =>
      switch (child) {
      | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Two
      | Three => no_movement
      }
    | ITE(t, _) =>
      switch (child) {
      | One => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Two
      | Three => no_movement
      }
    | TypFun(_, _, e1, _) =>
      switch (child) {
      | One => return_cursor(CursorBind(e))
      | Two => return_cursor(CursorExp(e1.child))
      | Three => no_movement
      }
    | TypAp(e1, _, t, _) =>
      switch (child) {
      | One => return_cursor(CursorExp(e1.child))
      | Two => return_cursor(CursorTyp(e, Cursor(t.contents)))
      | Three => no_movement
      }
    }
  | (CursorExp(e), Delete) =>
    let e': Iexp.upper = {
      parent: e.parent,
      syn: Some(Hole),
      middle: EHole,
      interval: e.interval,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };
    delete_upper(e);
    replace(e, e');
    let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(e'));
  | (CursorExp(_), InsertNumType)
  | (CursorExp(_), InsertBoolType)
  | (CursorExp(_), InsertUnitType)
  | (CursorExp(_), WrapArrow(_))
  | (CursorExp(_), InsertList)
  | (CursorExp(_), WrapProduct(_))
  | (CursorExp(_), WrapForAll)
  | (CursorExp(_), InsertTypVar(_)) => no_movement
  | (CursorExp(e), InsertNumLit(x)) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(Num),
        middle: NumLit(x),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertNil) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(List),
        middle: Nil,
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertCons) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(Arrow(Num, Arrow(List, List))),
        middle: Cons,
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertListRec) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn:
          Some(
            Arrow(
              Hole,
              Arrow(Arrow(Num, Arrow(Hole, Hole)), Arrow(List, Hole)),
            ),
          ),
        middle: ListRec(ref(Htyp.Hole), Hashtbl.create(0)),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertListMatch) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn:
          Some(
            Arrow(
              List,
              Arrow(Hole, Arrow(Arrow(Num, Arrow(List, Hole)), Hole)),
            ),
          ),
        middle: ListRec(ref(Htyp.Hole), Hashtbl.create(0)),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }

  | (CursorExp(e), InsertY) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(Arrow(Arrow(Hole, Hole), Hole)),
        middle: Y(ref(Htyp.Hole), Hashtbl.create(0)),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewY(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertLt) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(Arrow(Num, Arrow(Num, Bool))),
        middle: ListRec(ref(Htyp.Hole), Hashtbl.create(0)),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertITE) =>
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn:
          Some(
            Arrow(
              Bool,
              Arrow(Arrow(Unit, Hole), Arrow(Arrow(Unit, Hole), Hole)),
            ),
          ),
        middle: ListRec(ref(Htyp.Hole), Hashtbl.create(0)),
        interval: e.interval,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      delete_upper(e);
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), InsertVar(x)) =>
    switch (e.middle) {
    | EHole =>
      let (parent, ty, mark) =
        look_up_binder((x, BinderKind.Lam), e, binder_set, root);
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(ty),
        interval: e.interval,
        middle: Var(x, ref(mark), ref(parent)),
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      // switch (parent) {
      // | Root(_) => print_endline("isnerting to root")
      // | _ => print_endline("inserting ound")
      // };
      delete_upper(e);
      replace(e, e');
      bind_to_binder_var(e', parent);
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(e'));
    | _ => no_movement
    }
  | (CursorExp(e), WrapPlus(child)) =>
    let make_plus_with_children = (parent, interval, e1, e2, q) => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper(),
        ana: Some(Num),
        marked: Unmarked,
        child: e1,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper(),
        ana: Some(Num),
        marked: Unmarked,
        child: e2,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
      let new_upper: Iexp.upper = {
        parent,
        syn: Some(Num),
        interval,
        middle: new_mid,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };

      splice(new_lower_left, new_upper);
      splice(new_lower_right, new_upper);

      let update_list = [
        Update.NewAna(parent),
        Update.NewAna(Lower(new_lower_left)),
        Update.NewAna(Lower(new_lower_right)),
        Update.NewSyn(new_upper),
      ];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(new_upper));
    };
    let interval = interval_around(e);
    switch (child) {
    | One =>
      let hole = exp_hole_upper(interval_after(e));
      make_plus_with_children(e.parent, interval, e, hole, q);
    | Two =>
      let hole = exp_hole_upper(interval_before(e));
      make_plus_with_children(e.parent, interval, hole, e, q);
    | Three => no_movement
    };
  | (CursorExp(e), WrapAp(child)) =>
    let make_ap_with_children = (parent, interval, e1, e2, q) => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper(),
        ana: None,
        marked: Unmarked,
        child: e1,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper(),
        ana: Some(Hole),
        marked: Unmarked,
        child: e2,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_mid: Iexp.middle =
        Ap(new_lower_left, ref(Mark.Unmarked), new_lower_right);
      let new_upper: Iexp.upper = {
        parent,
        syn: Some(Hole),
        interval,
        middle: new_mid,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };

      splice(new_lower_left, new_upper);
      splice(new_lower_right, new_upper);
      let update_list = [
        Update.NewAna(new_upper.parent),
        Update.NewSyn(e1),
        Update.NewSyn(new_upper),
        switch (child) {
        | Child.One => Update.NewAna(Lower(new_lower_left))
        | Child.Two => Update.NewAna(Lower(new_lower_right))
        | Child.Three => raise(Unreachable)
        },
      ];

      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(new_upper));
    };
    // this must come before the calls to interval_before or _after. It mutates s.som.
    let interval = interval_around(e);
    switch (child) {
    | One =>
      let hole = exp_hole_upper(interval_after(e));
      make_ap_with_children(e.parent, interval, e, hole, q);
    | Two =>
      let hole = exp_hole_upper(interval_before(e));
      make_ap_with_children(e.parent, interval, hole, e, q);
    | Three => no_movement
    };
  | (CursorExp(body), WrapLam) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper(),
      ana: None,
      marked: Unmarked,
      child: body,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_mid =
      Iexp.Lam(
        ref(Bind.Hole),
        ref(Htyp.Hole),
        ref(Mark.Unmarked),
        ref(Mark.Unmarked),
        new_lower,
        ref(Tree.empty),
        Hashtbl.create(0),
      );
    let new_upper: Iexp.upper = {
      parent: body.parent,
      syn: None,
      interval: interval_around(body),
      middle: new_mid,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower, new_upper);

    let update_list = [
      Update.NewAna(new_upper.parent),
      Update.NewAna(Lower(new_lower)),
      Update.NewSyn(body),
      Update.NewSyn(new_upper),
    ];
    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(new_upper));

  | (CursorExp(body), WrapTypFun) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper(),
      ana: None,
      marked: Unmarked,
      child: body,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_mid =
      Iexp.TypFun(
        ref(Bind.Hole),
        ref(Mark.Unmarked),
        new_lower,
        ref(Tree.empty),
      );
    let new_upper: Iexp.upper = {
      parent: body.parent,
      syn: None,
      interval: interval_around(body),
      middle: new_mid,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower, new_upper);

    let update_list = [
      Update.NewAna(new_upper.parent),
      Update.NewAna(Lower(new_lower)),
      Update.NewSyn(body),
      Update.NewSyn(new_upper),
    ];
    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(new_upper));

  | (CursorExp(e), WrapTypAp) =>
    // this must come before the calls to interval_before or _after. It mutates s.som.
    let interval = interval_around(e);
    let new_lower_left: Iexp.lower = {
      upper: dummy_upper(),
      ana: None,
      marked: Unmarked,
      child: e,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_mid: Iexp.middle =
      TypAp(
        new_lower_left,
        ref(Mark.Unmarked),
        ref(Htyp.Hole),
        Hashtbl.create(0),
      );
    let new_upper: Iexp.upper = {
      parent: e.parent,
      syn: Some(Hole),
      interval,
      middle: new_mid,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower_left, new_upper);
    let update_list = [
      Update.NewAna(new_upper.parent),
      Update.NewSyn(e),
      Update.NewSyn(new_upper),
      Update.NewAna(Lower(new_lower_left)),
    ];

    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(new_upper));

  | (CursorExp(e), WrapPair(child)) =>
    let make_product_with_children = (parent, interval, e1, e2, q, child) => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper(),
        ana: None,
        marked: Unmarked,
        child: e1,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper(),
        ana: None,
        marked: Unmarked,
        child: e2,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_mid: Iexp.middle =
        Pair(new_lower_left, new_lower_right, ref(Mark.Unmarked));
      let new_upper: Iexp.upper = {
        parent,
        syn: None,
        interval,
        middle: new_mid,
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };

      splice(new_lower_left, new_upper);
      splice(new_lower_right, new_upper);

      let update_list = [
        Update.NewAna(parent),
        Update.NewSyn(e1),
        Update.NewSyn(e2),
        Update.NewSyn(new_upper),
        switch (child) {
        | Child.One => Update.NewAna(Lower(new_lower_left))
        | Child.Two => Update.NewAna(Lower(new_lower_right))
        | Child.Three => raise(Unreachable)
        },
      ];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(new_upper));
    };
    let interval = interval_around(e);
    switch (child) {
    | One =>
      let hole = exp_hole_upper(interval_after(e));
      make_product_with_children(e.parent, interval, e, hole, q, Child.One);
    | Two =>
      let hole = exp_hole_upper(interval_before(e));
      make_product_with_children(e.parent, interval, hole, e, q, Child.Two);
    | Three => no_movement
    };

  | (CursorExp(e), WrapProj(prod_side)) =>
    let parent = e.parent;
    let interval = interval_around(e);
    let new_lower: Iexp.lower = {
      upper: dummy_upper(),
      ana: None,
      marked: Unmarked,
      child: e,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_middle: Iexp.middle =
      Proj(prod_side, new_lower, ref(Mark.Unmarked));
    let new_upper: Iexp.upper = {
      parent,
      syn: None,
      interval,
      middle: new_middle,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower, new_upper);

    let update_list = [
      Update.NewAna(parent),
      Update.NewSyn(e),
      Update.NewAna(Lower(new_lower)),
      Update.NewSyn(new_upper),
    ];
    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(new_upper));

  | (CursorExp(e), WrapAsc) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper(),
      ana: Some(Hole),
      marked: Unmarked,
      child: e,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_mid: Iexp.middle =
      Asc(new_lower, ref(Htyp.Hole), Hashtbl.create(0));
    let new_upper: Iexp.upper = {
      parent: e.parent,
      syn: Some(Hole),
      interval: interval_around(e),
      middle: new_mid,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower, new_upper);

    let update_list = [
      Update.NewAna(new_upper.parent),
      Update.NewSyn(new_upper),
      Update.NewAna(Lower(new_lower)),
    ];
    UpdateQueue.update_push_list(update_list, q);
    return_cursor(CursorExp(new_upper));

  | (CursorExp(e), Unwrap(child)) =>
    switch (e.middle) {
    | EHole => no_movement
    | Var(_, _, _)
    | NumLit(_)
    | Nil
    | Cons
    | ListRec(_)
    | ITE(_)
    | Y(_) => apply_action(state, Delete)
    | Lam(bind, _, _, _, body_lower, bound_vars, _) =>
      let body = body_lower.child;
      let parent = e.parent;
      let bound_var_set = bound_vars.contents;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      replace(e, body);

      // update bound variables to outer binder
      switch (bind.contents) {
      | Hole => ()
      | Var(x) =>
        remove_from_binder_set((x, BinderKind.Lam), e, binder_set);
        let (new_binder, t, m) =
          look_up_binder((x, BinderKind.Lam), e, binder_set, root);
        add_bound_var_set((x, BinderKind.Lam), bound_var_set, new_binder);

        let update = var => update_var(var, t, m, new_binder);
        Tree.iter(update, bound_var_set);
      };

      // because updating vars could have deleted the body
      let new_body = child_of_parent(parent);

      // todo: maybe this could be a stream so that we don't have to wast time
      // appending sublists
      let bound_vars_list = Tree.list_of_t(bound_var_set);
      let update_list =
        [Update.NewAna(parent)]
        @ List.map(e => Update.NewSyn(e), bound_vars_list)
        @ [Update.NewSyn(new_body)];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(new_body));

    | Ap(fun_lower, _, arg_lower) =>
      let (body_lower, deleted_lower) =
        switch (child) {
        | One => (fun_lower, arg_lower)
        | Two => (arg_lower, fun_lower)
        | Three => raise(Unimplemented)
        };
      let body = body_lower.child;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      delete_lower(deleted_lower);
      replace(e, body);

      let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(body));

    | Plus(left_arg, right_arg)
    | Pair(left_arg, right_arg, _) =>
      let (body_lower, deleted_lower) =
        switch (child) {
        | One => (left_arg, right_arg)
        | Two => (right_arg, left_arg)
        | Three => raise(Unimplemented)
        };
      let body = body_lower.child;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      delete_lower(deleted_lower);
      replace(e, body);

      let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(body));

    | Proj(_, body_lower, _)
    | Asc(body_lower, _, _) =>
      let body = body_lower.child;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      replace(e, body);

      let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(body));
    | TypFun(bind, _, body_lower, bound_vars) =>
      let body = body_lower.child;
      let parent = e.parent;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      replace(e, body);

      // update bound variables to outer binder
      switch (bind.contents) {
      | Hole => ()
      | Var(x) =>
        remove_from_binder_set((x, BinderKind.TypFun), e, binder_set);

        // Binder -> Boundvars
        let (new_binder, _, m) =
          look_up_binder((x, BinderKind.TypFun), e, binder_set, root);
        add_bound_var_set((x, BinderKind.TypFun), bound_vars^, new_binder);

        // Boundvars -> Binder
        let update = (containing_upper: Iexp.upper) => {
          let t = typ_ref_of_upper(containing_upper);
          t := htyp_update_mark(t^, x, m);
          Hashtbl.replace(
            typ_binders_of_upper(containing_upper),
            x,
            new_binder,
          );
        };
        Tree.iter(update, bound_vars^);
      };

      // because updating vars could have deleted the body
      let new_body = child_of_parent(parent);

      // todo: maybe this could be a stream so that we don't have to wast time
      // appending sublists
      let bound_vars_list = Tree.list_of_t(bound_vars^);
      let update_list =
        [Update.NewAna(parent)]
        @ List.map(e => Update.NewSyn(e), bound_vars_list)
        @ [Update.NewSyn(new_body)]; // TODO: Doublecheck this
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(new_body));
    | TypAp(fun_lower, _, _, _) =>
      let body = fun_lower.child;

      e.deleted_upper = true;
      fun_lower.deleted_lower = true;
      replace(e, body);

      let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
      UpdateQueue.update_push_list(update_list, q);
      return_cursor(CursorExp(body));
    }
  };
};

let apply_actions = (actions: list(Iaction.t), s): Istate.t => {
  List.fold_left(apply_action, s, actions);
};
