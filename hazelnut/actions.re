open Sexplib.Std;
open Hazelnut;
open Order;
open Incremental;
open State;
open UpdateQueue;

// open Monad_lib.Monad;

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
    | WrapLam
    | WrapAsc
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

// Finds the looks up [name] in the context of [e].
// Returns the binding site (or root), the synthesized type, and whether [name] is free.
let rec look_up_binder =
        (parent: Iexp.parent, name: string): (Iexp.parent, Htyp.t, Mark.t) => {
  switch (parent) {
  | Deleted
  | Root(_) => (parent, Hole, Marked)
  | Lower(lower) =>
    // print_endline("found lower while unshadowing...");
    switch (lower.upper.middle) {
    | Lam(bind, lam_ty, _, _, _, _) =>
      // print_endline("... it's a lam ...");
      if (bind.contents == Var(name)) {
        (
          // print_endline("... a match!");
          parent,
          lam_ty.contents,
          Unmarked,
        );
      } else {
        // print_endline("... not a match.");
        look_up_binder(
          lower.upper.parent,
          name,
        );
      }
    | _ =>
      // print_endline("... it's not a lam.");
      look_up_binder(lower.upper.parent, name)
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

let bind_to_binder = (var: Iexp.upper, parent: Iexp.parent) => {
  switch (parent) {
  | Deleted
  | Root(_) => ()
  | Lower(lower) =>
    switch (lower.upper.middle) {
    | Lam(_, _, _, _, _, bound_vars) => Iexp.add_bound_var(var, bound_vars)
    | _ => ()
    }
  };
};

// precondition: e.middle is a Var
// makes them all synthesize [syn], marks them all as [m], and updates their
// binding on both ends. It also marks them as on the update queue with new syn.
let update_var =
    (e: Iexp.upper, syn: Htyp.t, m: Mark.t, new_binder: Iexp.binder) => {
  switch (e.middle) {
  | Var(var_name, _, old_binder) =>
    // remove this var from its previous binder
    unbind_from_binder(e, old_binder);
    // set the local binder, mark, and syn type
    let new_mid: Iexp.middle = Var(var_name, m, new_binder);

    let new_upper: Iexp.upper = {
      parent: e.parent,
      syn: Some(syn),
      middle: new_mid,
      interval: e.interval,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };
    replace(e, new_upper);
    new_upper;
  | _ => failwith("update_var called on non-var")
  };
};

// Finds all (syntactically) free variables with given name, updates them,
// and returns them as a list.
let rec capture_name =
        (e: Iexp.upper, name: string, syn: Htyp.t, binder: Iexp.binder)
        : list(Iexp.upper) => {
  switch (e.middle) {
  | Var(var_name, _, _) =>
    if (name == var_name) {
      [
        // print_endline("capturing " ++ var_name);
        update_var(e, syn, Unmarked, binder),
      ];
    } else {
      [];
    }
  | NumLit(_) => []
  | Plus(lower_a, lower_b) =>
    List.append(
      capture_name(lower_a.child, name, syn, binder),
      capture_name(lower_b.child, name, syn, binder),
    )
  | Lam(bind, _, _, _, body_lower, _) =>
    if (bind.contents == Var(name)) {
      [];
    } else {
      capture_name(body_lower.child, name, syn, binder);
    }
  | Ap(actor, _, param) =>
    List.append(
      capture_name(actor.child, name, syn, binder),
      capture_name(param.child, name, syn, binder),
    )
  | Asc(lower, _) => capture_name(lower.child, name, syn, binder)
  | EHole => []
  };
};

// let capture_name_with_updates =
//     (e: Iexp.upper, name: string, syn: Htyp.t, binder: Iexp.binder) => {
//   let newly_bound = capture_name(e, name, syn, binder);
//   let captured_updates = List.map(e => Update.NewSyn(e), newly_bound);
//   (newly_bound, captured_updates);
// };

let rec delete_lower = (e: Iexp.lower) => {
  e.deleted_lower = true;
  delete_upper(e.child);
}

and delete_middle = (e: Iexp.middle) => {
  switch (e) {
  | EHole
  | Var(_)
  | NumLit(_) => ()
  | Asc(e, _) => delete_lower(e)
  | Lam(_, _, _, _, e, _) => delete_lower(e)
  | Plus(e1, e2) =>
    delete_lower(e1);
    delete_lower(e2);
  | Ap(e1, _, e2) =>
    delete_lower(e1);
    delete_lower(e2);
  };
}

and delete_upper = (e: Iexp.upper) => {
  e.deleted_upper = true;
  delete_middle(e.middle);
};

let add_two = b => {
  let c = Order.add_next(b);
  let d = Order.add_next(c);
  (c, d);
};

let interval_around = (e: Iexp.upper) => {
  let (a, b) = e.interval;
  let (c, d) = add_two(b);
  // a < b < c < d
  e.interval = (b, c);
  (a, d);
};

let interval_after = (e: Iexp.upper) => {
  let (_a, b) = e.interval;
  let (c, d) = add_two(b);
  // a < b < c < d
  (c, d);
};

let interval_before = (e: Iexp.upper) => {
  let (a, b) = e.interval;
  let (c, d) = add_two(b);
  // a < b < c < d
  e.interval = (c, d);
  (a, b);
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
  | (z, WrapLam) => z
  };
};

let rec apply_action = (s: Istate.t, a: Iaction.t): Istate.t => {
  let no_op = s;
  let c = s.c;
  let q = s.q;

  print_endline(
    string_of_int(List.length(UpdateQueue.list_of_t(q))) ++ " updates.",
  );

  switch (c) {
  | CursorExp(e) when e.parent == Deleted =>
    failwith("cursor has deleted parent :(")
  | _ => ()
  };

  switch (c, a) {
  | (CursorBind(e), MoveUp) => {...s, c: CursorExp(e)}
  | (CursorBind(e), Delete) =>
    switch (e.middle) {
    | Lam(bind, _t, _m1, _m2, body, bound_vars) =>
      switch (bind.contents) {
      | Var(x) =>
        bind.contents = Hole;
        let (new_binder, t, m) = look_up_binder(e.parent, x);

        let update = var => update_var(var, t, m, new_binder);
        let newly_bound = List.map(update, bound_vars.contents);

        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => Update.NewSyn(e), newly_bound)
          @ [NewAna(Lower(body)), NewSyn(body.child)];
        {c, q: UpdateQueue.update_push_list(update_list, q)};
      | Hole => no_op
      }
    | _ => failwith("CursorBind on non lambda")
    }
  | (CursorBind(e), InsertVar(x)) =>
    switch (e.middle) {
    | Lam(bind, t, _m1, _m2, body, bound_vars) =>
      switch (bind.contents) {
      | Hole =>
        bind.contents = Var(x);
        let newly_bound =
          capture_name(body.child, x, t.contents, Iexp.Lower(body));
        bound_vars.contents = newly_bound;
        let update_list =
          [Update.NewAna(e.parent)]
          @ List.map(e => Update.NewSyn(e), newly_bound)
          @ [NewAna(Lower(body)), NewSyn(body.child)];
        {c, q: UpdateQueue.update_push_list(update_list, q)};
      | Var(_) => no_op
      }
    | _ => failwith("CursorBind on non lambda")
    }
  | (CursorBind(_), _) => no_op
  | (CursorTyp(e, Cursor(_)), MoveUp) => {...s, c: CursorExp(e)}
  | (CursorTyp(e, z), a) =>
    switch (e.middle) {
    | Lam(_, t, _m1, _m2, _body, _bound) =>
      let z' = apply_action_typ(z, a);
      let t' = erase_typ(z');
      t.contents = t';
      {c: CursorTyp(e, z'), q: UpdateQueue.update_push(NewAnn(e), q)};
    | Asc(_, t) =>
      let z' = apply_action_typ(z, a);
      let t' = erase_typ(z');
      t.contents = t';
      {c: CursorTyp(e, z'), q: UpdateQueue.update_push(NewAsc(e), q)};
    | _ => failwith("CursorTyp on node with no type")
    }
  | (CursorExp(e), MoveUp) =>
    switch (upper_of_parent(e.parent)) {
    | None => no_op
    | Some(e') => {...s, c: CursorExp(e')}
    }
  | (CursorExp(e), MoveDown(child)) =>
    switch (e.middle) {
    | Var(_, _, _)
    | NumLit(_)
    | EHole => no_op
    | Plus(e1, e2)
    | Ap(e1, _, e2) =>
      switch (child) {
      | One => {...s, c: CursorExp(e1.child)}
      | Two => {...s, c: CursorExp(e2.child)}
      | Three => no_op
      }
    | Lam(_, t, _, _, e1, _) =>
      switch (child) {
      | One => {...s, c: CursorBind(e)}
      | Two => {...s, c: CursorTyp(e, Cursor(t.contents))}
      | Three => {...s, c: CursorExp(e1.child)}
      }
    | Asc(e1, t) =>
      switch (child) {
      | One => {...s, c: CursorExp(e1.child)}
      | Two => {...s, c: CursorTyp(e, Cursor(t.contents))}
      | Three => no_op
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
    {c: CursorExp(e'), q: UpdateQueue.update_push_list(update_list, q)};
  | (CursorExp(_), InsertNumType)
  | (CursorExp(_), WrapArrow(_)) => no_op
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
      replace(e, e');
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      {c: CursorExp(e'), q: UpdateQueue.update_push_list(update_list, q)};
    | _ => no_op
    }
  | (CursorExp(e), InsertVar(x)) =>
    print_endline(
      switch (e.parent) {
      | Deleted => "DELETED PARENT OF CURSOR??"
      | _ => "oh okay"
      },
    );
    switch (e.middle) {
    | EHole =>
      let (parent, ty, mark) = look_up_binder(e.parent, x);
      let e': Iexp.upper = {
        parent: e.parent,
        syn: Some(ty),
        interval: e.interval,
        middle: Var(x, mark, parent),
        in_queue_upper: InQueue.default_upper(),
        deleted_upper: false,
      };
      replace(e, e');
      bind_to_binder(e', parent);
      let update_list = [Update.NewAna(e'.parent), Update.NewSyn(e')];
      let q' = UpdateQueue.update_push_list(update_list, q);
      {c: CursorExp(e'), q: q'};
    | _ => no_op
    };
  | (CursorExp(e), WrapPlus(child)) =>
    let make_plus_with_children = (parent, interval, e1, e2, q): Istate.t => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: Some(Num),
        marked: Unmarked,
        child: e1,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
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

      {
        c: CursorExp(new_upper),
        q: UpdateQueue.update_push_list(update_list, q),
      };
    };
    let interval = interval_around(e);
    switch (child) {
    | One =>
      let hole = exp_hole_upper(interval_after(e));
      make_plus_with_children(e.parent, interval, e, hole, q);
    | Two =>
      let hole = exp_hole_upper(interval_before(e));
      make_plus_with_children(e.parent, interval, hole, e, q);
    | Three => no_op
    };
  | (CursorExp(e), WrapAp(child)) =>
    let make_ap_with_children = (parent, interval, e1, e2, q): Istate.t => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: None,
        marked: Unmarked,
        child: e1,
        in_queue_lower: InQueue.default_lower(),
        deleted_lower: false,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
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
        Update.NewAna(Lower(new_lower_left)),
      ];
      {
        c: CursorExp(new_upper),
        q: UpdateQueue.update_push_list(update_list, q),
      };
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
    | Three => no_op
    };
  | (CursorExp(body), WrapLam) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper,
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
        ref([]),
      );
    let new_upper: Iexp.upper = {
      parent: body.parent,
      syn: body.syn,
      interval: interval_around(body),
      middle: new_mid,
      in_queue_upper: InQueue.default_upper(),
      deleted_upper: false,
    };

    splice(new_lower, new_upper);

    let update_list = [
      Update.NewAna(new_upper.parent),
      NewAna(Lower(new_lower)),
      NewSyn(body),
    ];
    {
      c: CursorExp(new_upper),
      q: UpdateQueue.update_push_list(update_list, q),
    };

  | (CursorExp(e), WrapAsc) =>
    let new_lower: Iexp.lower = {
      upper: dummy_upper,
      ana: Some(Hole),
      marked: Unmarked,
      child: e,
      in_queue_lower: InQueue.default_lower(),
      deleted_lower: false,
    };
    let new_mid: Iexp.middle = Asc(new_lower, ref(Htyp.Hole));
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

    {
      c: CursorExp(new_upper),
      q: UpdateQueue.update_push_list(update_list, q),
    };

  | (CursorExp(e), Unwrap(child)) =>
    switch (e.middle) {
    | EHole => no_op
    | Var(_, _, _)
    | NumLit(_) => apply_action(s, Delete)
    | Lam(bind, _, _, _, body_lower, bound_vars) =>
      let body = body_lower.child;
      let parent = e.parent;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      replace(e, body);

      // update bound variables to outer binder
      let newly_bound =
        switch (bind.contents) {
        | Hole => []
        | Var(x) =>
          let (new_binder, t, m) = look_up_binder(parent, x);
          // switch (m) {
          // | Unmarked => print_endline("Found unshadow")
          // | Marked => print_endline("No unshadow found")
          // };
          let update = var => update_var(var, t, m, new_binder);
          List.map(update, bound_vars.contents);
        };

      // because updating vars could have deleted the body
      let new_body = child_of_parent(parent);

      let update_list =
        [Update.NewAna(parent)]
        @ List.map(e => Update.NewSyn(e), newly_bound)
        @ [Update.NewSyn(new_body)];
      {
        c: CursorExp(new_body),
        q: UpdateQueue.update_push_list(update_list, q),
      };

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
      {c: CursorExp(body), q: UpdateQueue.update_push_list(update_list, q)};

    | Plus(left_arg, right_arg) =>
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
      {c: CursorExp(body), q: UpdateQueue.update_push_list(update_list, q)};

    | Asc(body_lower, _ty) =>
      let body = body_lower.child;

      e.deleted_upper = true;
      body_lower.deleted_lower = true;
      replace(e, body);

      let update_list = [Update.NewAna(body.parent), Update.NewSyn(body)];
      {c: CursorExp(body), q: UpdateQueue.update_push_list(update_list, q)};
    }
  };
};
