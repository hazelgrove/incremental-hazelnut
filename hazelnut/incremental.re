open Sexplib.Std;
open Hazelnut;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

module Iexp = {
  [@deriving sexp]
  type lower = {
    mutable upper,
    ana: option(Htyp.t),
    mutable marked: bool,
    mutable child: upper,
  }

  and middle =
    | Var(string, bool, binder)
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(string, ref(Htyp.t), bool, bool, lower, bound_vars)
    | Ap(lower, bool, lower)
    | Asc(lower, ref(Htyp.t))
    | EHole

  and upper = {
    mutable parent,
    syn: option(Htyp.t),
    middle,
  }

  and child_ref = {mutable root_child: upper}

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(child_ref) // root of the main program
    | Lower(lower) // child location of a constuctor

  and binder = parent // pointer from a variable occurrence to binding location
  and bound_vars = ref(list(upper)); // pointers from a binder to the variable occurrences it binds

  // let add_bound_var = (var: upper, bound_vars: bound_vars) => {
  //   bound_vars.contents = [var, ...bound_vars.contents];
  // };

  let remove_bound_var = (var: upper, bound_vars: bound_vars) => {
    bound_vars.contents =
      List.filter(var' => var !== var', bound_vars.contents);
  };
};

module Update = {
  [@deriving sexp]
  type t =
    | NewSyn(Iexp.upper)
    | NewAna(Iexp.lower)
    | NewAnn(Iexp.upper)
    | NewAsc(Iexp.upper);
};

module UpdateQueue = {
  [@deriving sexp]
  type t = list(Update.t);
  let push = (u, q: t) => [u, ...q];
  let push_list = (u: list(Update.t), q: t) =>
    List.fold_left((q', u') => push(u', q'), q, u);
  let pop = (q: t) =>
    switch (q) {
    | [] => None
    | [u, ..._] => Some(u)
    };
};

module Icursor = {
  [@deriving sexp]
  type t =
    | CursorExp(Iexp.upper)
    | CursorTyp(Iexp.upper, Ztyp.t);
};

module Istate = {
  [@deriving sexp]
  type t = (Icursor.t, UpdateQueue.t);
};

let exp_hole_upper: unit => Iexp.upper =
  () => {parent: Deleted, syn: Some(Hole), middle: EHole};

let initial_exp = exp_hole_upper();

let initial_root: Iexp.parent = {
  let r: Iexp.child_ref = {root_child: initial_exp};
  initial_exp.parent = Root(r);
  Root(r);
};

let initial_cursor: Icursor.t = CursorExp(initial_exp);
let initial_state: Istate.t = (initial_cursor, []);

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
    | InsertNumLit(int)
    | InsertVar(string)
    | WrapPlus(Child.t)
    | WrapAp(Child.t)
    | WrapLam(string)
    | WrapAsc
    | Unwrap(Child.t); // The child argument is only relevant for the Ap case
};

let dummy_upper = exp_hole_upper();

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

let freshen_ana_parent = (parent: Iexp.parent): list(Update.t) => {
  switch (parent) {
  | Deleted
  | Root(_) => []
  | Lower(lower) => [Update.NewAna(lower)]
  };
};

// Finds the looks up [name] in the context of [e].
// Returns the binding site (or root), the synthesized type, and whether [name] is free.
let rec look_up_binder =
        (e: Iexp.upper, name: string): (Iexp.parent, Htyp.t, bool) => {
  switch (e.parent) {
  | Deleted
  | Root(_) => (e.parent, Hole, true)
  | Lower(lower) =>
    switch (lower.upper.middle) {
    | Lam(lam_name, lam_ty, _, _, _, _) =>
      if (name == lam_name) {
        (e.parent, lam_ty.contents, false);
      } else {
        look_up_binder(lower.upper, name);
      }
    | _ => look_up_binder(lower.upper, name)
    }
  };
};

let unbind_from_binder = (var: Iexp.upper, parent: Iexp.parent) => {
  switch (parent) {
  | Deleted
  | Root(_) => ()
  | Lower(lower) =>
    switch (lower.upper.middle) {
    | Lam(_, _, _, _, _, bound_vars) =>
      Iexp.remove_bound_var(var, bound_vars)
    | _ => ()
    }
  };
};

// precondition: e.middle is a Var//
// makes them all synthesize [syn], marks them all as [m], and updates their
// binding on both ends.
let update_var = (e: Iexp.upper, syn: Htyp.t, m: bool, binder: Iexp.binder) => {
  switch (e.middle) {
  | Var(var_name, _, old_binder) =>
    // remove this var from its previous binder
    unbind_from_binder(e, old_binder);
    // set the local binder, mark, and syn type
    let m': Iexp.middle = Var(var_name, m, binder);
    let e': Iexp.upper = {parent: e.parent, syn: Some(syn), middle: m'};
    set_child_in_parent(e.parent, e');
    e';
  | _ => failwith("update_var called on non-var")
  };
};

// Finds all (syntactically) free variables with given name, updates them,
// and returns them as a list.
let rec capture_name =
        (
          e: Iexp.upper,
          name: string,
          syn: Htyp.t,
          m: bool,
          binder: Iexp.binder,
        )
        : list(Iexp.upper) => {
  switch (e.middle) {
  | Var(var_name, _, _) =>
    if (name == var_name) {
      let e' = update_var(e, syn, m, binder);
      [e'];
    } else {
      [];
    }
  | NumLit(_) => []
  | Plus(lower_a, lower_b) =>
    List.append(
      capture_name(lower_a.child, name, syn, m, binder),
      capture_name(lower_b.child, name, syn, m, binder),
    )
  | Lam(lam_name, _, _, _, body_lower, _) =>
    if (name == lam_name) {
      [];
    } else {
      capture_name(body_lower.child, name, syn, m, binder);
    }
  | Ap(actor, _, param) =>
    List.append(
      capture_name(actor.child, name, syn, m, binder),
      capture_name(param.child, name, syn, m, binder),
    )
  | Asc(lower, _) => capture_name(lower.child, name, syn, m, binder)
  | EHole => []
  };
};

let rec apply_action_typ = (z: Ztyp.t, a: Iaction.t): Ztyp.t => {
  switch (z, a) {
  | (Cursor(_), MoveUp) => z
  | (LArrow(Cursor(t1), t2), MoveUp)
  | (RArrow(t1, Cursor(t2)), MoveUp) => Cursor(Arrow(t1, t2))
  | (Cursor(Hole), MoveDown(_)) => z
  | (Cursor(Num), MoveDown(_)) => z
  | (Cursor(Arrow(t1, t2)), MoveDown(One)) => LArrow(Cursor(t1), t2)
  | (Cursor(Arrow(t1, t2)), MoveDown(Two)) => RArrow(t1, Cursor(t2))
  | (Cursor(Arrow(_)), MoveDown(Three)) => z
  | (Cursor(_), Delete) => Cursor(Hole)
  | (Cursor(Hole), InsertNumType) => Cursor(Num)
  | (Cursor(_), InsertNumType) => z
  | (Cursor(t), WrapArrow(One)) => Cursor(Arrow(t, Hole))
  | (Cursor(t), WrapArrow(Two)) => Cursor(Arrow(Hole, t))
  | (Cursor(_), WrapArrow(Three)) => z
  | (Cursor(Hole), Unwrap(_)) => z
  | (Cursor(Num), Unwrap(_)) => z
  | (Cursor(Arrow(t, _)), Unwrap(One))
  | (Cursor(Arrow(_, t)), Unwrap(Two)) => Cursor(t)
  | (Cursor(Arrow(_)), Unwrap(Three)) => z
  | (LArrow(z, t), MoveUp)
  | (LArrow(z, t), MoveDown(_))
  | (LArrow(z, t), Delete)
  | (LArrow(z, t), InsertNumType)
  | (LArrow(z, t), WrapArrow(_))
  | (LArrow(z, t), Unwrap(_)) => LArrow(apply_action_typ(z, a), t)
  | (RArrow(t, z), MoveUp)
  | (RArrow(t, z), MoveDown(_))
  | (RArrow(t, z), Delete)
  | (RArrow(t, z), InsertNumType)
  | (RArrow(t, z), WrapArrow(_))
  | (RArrow(t, z), Unwrap(_)) => RArrow(t, apply_action_typ(z, a))
  | (z, WrapAsc) => z
  | (z, InsertNumLit(_)) => z
  | (z, InsertVar(_)) => z
  | (z, WrapPlus(_)) => z
  | (z, WrapAp(_)) => z
  | (z, WrapLam(_)) => z
  };
};

let rec apply_action = ((c, q): Istate.t, a: Iaction.t): Istate.t => {
  let no_op = (c, q);
  switch (c, a) {
  | (CursorTyp(e, Cursor(_)), MoveUp) => (CursorExp(e), q)
  | (CursorTyp(e, z), a) =>
    switch (e.middle) {
    | Lam(_, t, _m1, _m2, _body, _bound) =>
      let z' = apply_action_typ(z, a);
      let t' = erase_typ(z');
      t.contents = t';
      (CursorTyp(e, z'), UpdateQueue.push(NewAnn(e), q));
    | Asc(_, t) =>
      let z' = apply_action_typ(z, a);
      let t' = erase_typ(z');
      t.contents = t';
      (CursorTyp(e, z'), UpdateQueue.push(NewAsc(e), q));
    | _ => failwith("CursorTyp on node with no type")
    }
  | (CursorExp(e), MoveUp) =>
    switch (upper_of_parent(e.parent)) {
    | None => no_op
    | Some(e') => (CursorExp(e'), q)
    }
  | (CursorExp(e), MoveDown(child)) =>
    switch (e.middle) {
    | Var(_, _, _)
    | NumLit(_)
    | EHole => no_op
    | Plus(e1, e2) =>
      switch (child) {
      | One => (CursorExp(e1.child), q)
      | Two => (CursorExp(e2.child), q)
      | Three => no_op
      }
    | Lam(_, t, _, _, e1, _) =>
      switch (child) {
      | One => (CursorTyp(e, Cursor(t.contents)), q)
      | Two => (CursorExp(e1.child), q)
      | Three => no_op
      }
    | Ap(e1, _, e2) =>
      switch (child) {
      | One => (CursorExp(e1.child), q)
      | Two => (CursorExp(e2.child), q)
      | Three => no_op
      }
    | Asc(e1, t) =>
      switch (child) {
      | One => (CursorExp(e1.child), q)
      | Two => (CursorTyp(e, Cursor(t.contents)), q)
      | Three => no_op
      }
    }
  | (CursorExp(e), Delete) =>
    let e': Iexp.upper = {parent: e.parent, syn: Some(Hole), middle: EHole};
    replace(e, e');
    let update_list = freshen_ana_parent(e'.parent) @ [Update.NewSyn(e')];
    (CursorExp(e'), UpdateQueue.push_list(update_list, q));
  | (CursorExp(_), InsertNumType)
  | (CursorExp(_), WrapArrow(_)) => no_op
  | (CursorExp(e), InsertNumLit(x)) =>
    // Numlits have no lower Iexp, so we can just create a new upper for it to link to the NumLit middle
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(Num),
        middle: NumLit(x),
      };
      replace(e, e');
      let update_list = freshen_ana_parent(e'.parent) @ [Update.NewSyn(e')];
      (CursorExp(e'), UpdateQueue.push_list(update_list, q));
    | _ => no_op
    }
  | (CursorExp(e), InsertVar(x)) =>
    switch (e.middle) {
    | EHole =>
      let (parent, ty, mark) = look_up_binder(e, x);
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(ty),
        middle: Var(x, mark, parent),
      };
      replace(e, e');
      let update_list = freshen_ana_parent(e'.parent) @ [Update.NewSyn(e')];
      (CursorExp(e'), UpdateQueue.push_list(update_list, q));
    | _ => no_op
    }
  | (CursorExp(e), WrapPlus(child)) =>
    let make_plus_with_children = (parent, e1, e2, q): Istate.t => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: Some(Num),
        marked: false,
        child: e1,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
        ana: Some(Num),
        marked: false,
        child: e2,
      };
      let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
      let new_upper: Iexp.upper = {parent, syn: Some(Num), middle: new_mid};

      splice(new_lower_left, new_upper);
      splice(new_lower_right, new_upper);

      let update_list =
        freshen_ana_parent(parent)
        @ [
          Update.NewAna(new_lower_left),
          Update.NewAna(new_lower_right),
          Update.NewSyn(new_upper),
        ];

      (CursorExp(new_upper), UpdateQueue.push_list(update_list, q));
    };
    switch (child) {
    | One => make_plus_with_children(e.parent, e, exp_hole_upper(), q)
    | Two => make_plus_with_children(e.parent, exp_hole_upper(), e, q)
    | Three => no_op
    };
  | (CursorExp(e), WrapAp(child)) =>
    let make_ap_with_children = (parent, e1, e2, q): Istate.t => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: None,
        marked: false,
        child: e1,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
        ana: None,
        marked: false,
        child: e2,
      };
      let new_mid: Iexp.middle = Ap(new_lower_left, false, new_lower_right);
      let new_upper: Iexp.upper = {parent, syn: None, middle: new_mid};

      splice(new_lower_left, new_upper);
      splice(new_lower_right, new_upper);

      let update_list =
        freshen_ana_parent(new_upper.parent)
        @ [Update.NewSyn(e1), Update.NewAna(new_lower_left)];
      (CursorExp(new_upper), UpdateQueue.push_list(update_list, q));
    };
    switch (child) {
    | One => make_ap_with_children(e.parent, e, exp_hole_upper(), q)
    | Two => make_ap_with_children(e.parent, exp_hole_upper(), e, q)
    | Three => no_op
    };
  | (CursorExp(e), WrapLam(name)) =>
    // TODO: Are we going to support empty lambda names?
    let new_lower: Iexp.lower = {
      upper: dummy_upper,
      ana: None,
      marked: false,
      child: e,
    };
    let newly_bound =
      capture_name(e, name, Hole, false, Iexp.Lower(new_lower));
    let new_mid =
      Iexp.Lam(
        name,
        ref(Htyp.Hole),
        false,
        false,
        new_lower,
        ref(newly_bound),
      );
    let new_upper: Iexp.upper = {
      parent: e.parent,
      syn: e.syn,
      middle: new_mid,
    };

    splice(new_lower, new_upper);

    let update_list =
      freshen_ana_parent(new_upper.parent)
      @ List.map(e => Update.NewSyn(e), newly_bound)
      @ [NewAna(new_lower), NewSyn(e)];

    (CursorExp(new_upper), UpdateQueue.push_list(update_list, q));

  | (CursorExp(e), WrapAsc) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper,
      ana: None,
      marked: false,
      child: e,
    };
    let new_mid: Iexp.middle = Asc(new_lower, ref(Htyp.Hole));
    let new_upper: Iexp.upper = {
      parent: e.parent,
      syn: None,
      middle: new_mid,
    };

    splice(new_lower, new_upper);

    let update_list =
      freshen_ana_parent(new_upper.parent)
      @ [Update.NewSyn(new_upper), Update.NewAna(new_lower)];

    (CursorExp(new_upper), UpdateQueue.push_list(update_list, q));

  | (CursorExp(e), Unwrap(child)) =>
    switch (e.middle) {
    | EHole => no_op
    | Var(_, _, _)
    | NumLit(_) => apply_action((c, q), Delete)
    | Lam(name, _, _, _, body_lower, bound_vars) =>
      let body = body_lower.child;

      replace(e, body);

      // update bound variables to outer binder
      let (new_binder, t, m) = look_up_binder(e, name);
      let update = var => update_var(var, t, m, new_binder);
      let _ = List.map(update, bound_vars.contents);

      let update_list =
        freshen_ana_parent(body.parent) @ [Update.NewSyn(body)];
      (CursorExp(body), UpdateQueue.push_list(update_list, q));

    | Ap(fun_lower, _, arg_lower) =>
      let body =
        switch (child) {
        | One => fun_lower.child
        | Two => arg_lower.child
        | Three => raise(Unimplemented)
        };

      replace(e, body);

      let update_list =
        freshen_ana_parent(body.parent) @ [Update.NewSyn(body)];
      (CursorExp(body), UpdateQueue.push_list(update_list, q));

    | Plus(left_arg, right_arg) =>
      let body =
        switch (child) {
        | One => left_arg.child
        | Two => right_arg.child
        | Three => raise(Unimplemented)
        };

      replace(e, body);

      let update_list =
        freshen_ana_parent(body.parent) @ [Update.NewSyn(body)];
      (CursorExp(body), UpdateQueue.push_list(update_list, q));

    | Asc(body_lower, _ty) =>
      let body = body_lower.child;

      replace(e, body);

      let update_list =
        freshen_ana_parent(body.parent) @ [Update.NewSyn(body)];
      (CursorExp(body), UpdateQueue.push_list(update_list, q));
    }
  };
};

let update_step = ((e, q): Istate.t): option(Istate.t) => {
  let _ = (e, q);
  let _ = UpdateQueue.pop(q);
  None;
};

let _ = update_step;
