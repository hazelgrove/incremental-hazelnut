open Hazelnut;
open Incremental;
open Tree;
open Order;
// open Hashtbl;

type bareExp =
  | Var(string)
  | NumLit(int)
  | Plus(bareExp, bareExp)
  | Lam(Bind.t, Htyp.t, bareExp)
  | Ap(bareExp, bareExp)
  | Pair(bareExp, bareExp)
  | Proj(ProdSide.t, bareExp)
  | Asc(bareExp, Htyp.t)
  | Nil
  | Cons
  | ListRec(Htyp.t)
  | Y(Htyp.t)
  | ITE(Htyp.t)
  | EHole;

type markedExp =
  | Var(string, Mark.t)
  | NumLit(int)
  | Plus(markedExp, markedExp)
  | Lam(Bind.t, Htyp.t, Mark.t, Mark.t, markedExp)
  | Ap(markedExp, Mark.t, markedExp)
  | Pair(markedExp, markedExp, Mark.t)
  | Proj(ProdSide.t, markedExp, Mark.t)
  | Asc(markedExp, Htyp.t)
  | Nil
  | Cons
  | ListRec(Htyp.t)
  | Y(Htyp.t)
  | EHole
  | Subsume(markedExp, Mark.t);

let rec erase_lower = (e: Iexp.lower): bareExp => {
  erase_upper(e.child);
}
and erase_middle: Iexp.middle => bareExp =
  fun
  | Var(x, _, _) => Var(x)
  | NumLit(x) => NumLit(x)
  | Plus(e1, e2) => Plus(erase_lower(e1), erase_lower(e2))
  | Lam(x, t, _, _, e, _) => Lam(x.contents, t.contents, erase_lower(e))
  | Ap(e1, _, e2) => Ap(erase_lower(e1), erase_lower(e2))
  | Pair(e1, e2, _) => Pair(erase_lower(e1), erase_lower(e2))
  | Proj(prod_side, e, _) => Proj(prod_side, erase_lower(e))
  | Asc(e, t) => Asc(erase_lower(e), t.contents)
  | Nil => Nil
  | Cons => Cons
  | ITE(t) => ITE(t.contents)
  | ListRec(t) => ListRec(t.contents)
  | Y(t) => Y(t.contents)
  | EHole => EHole
and erase_upper = (e: Iexp.upper): bareExp => {
  erase_middle(e.middle);
};

module Ctx = {
  type t = Hashtbl.t(string, Htyp.t);

  let lookup = (ctx: t, x: string): (Htyp.t, Mark.t) => {
    switch (Hashtbl.find_opt(ctx, x)) {
    | None => (Hole, Marked)
    | Some(t) => (t, Unmarked)
    };
  };

  let empty: t = Hashtbl.create(100);

  let extend_bind = (ctx: t, x: Bind.t, t: Htyp.t) => {
    switch (x) {
    | Hole => ()
    | Var(x) => Hashtbl.add(ctx, x, t)
    };
  };

  let remove_bind = (ctx: t, x: Bind.t) => {
    switch (x) {
    | Hole => ()
    | Var(x) => Hashtbl.remove(ctx, x)
    };
  };
};

let rec performance_mark_syn = (ctx: Ctx.t): (bareExp => (markedExp, Htyp.t)) =>
  fun
  | Var(x) => {
      let (t, m) = Ctx.lookup(ctx, x);
      (Var(x, m), t);
    }
  | NumLit(x) => (NumLit(x), Num)
  | Plus(e1, e2) => (
      Plus(
        performance_mark_ana(ctx, Num, e1),
        performance_mark_ana(ctx, Num, e2),
      ),
      Num,
    )
  | Lam(x, t, e) => {
      Ctx.extend_bind(ctx, x, t);
      let (body, syn) = performance_mark_syn(ctx, e);
      Ctx.remove_bind(ctx, x);
      (Lam(x, t, Mark.Unmarked, Mark.Unmarked, body), Arrow(t, syn));
    }
  | Ap(b1, b2) => {
      let (e1, syn) = performance_mark_syn(ctx, b1);
      let (t1, t2, m) = matched_arrow_typ(syn);
      let e2 = performance_mark_ana(ctx, t1, b2);
      (Ap(e1, m, e2), t2);
    }
  | Pair(b1, b2) => {
      let (e1, syn1) = performance_mark_syn(ctx, b1);
      let (e2, syn2) = performance_mark_syn(ctx, b2);
      (Pair(e1, e2, Unmarked), Product(syn1, syn2));
    }
  | Proj(prod_side, b) => {
      let (e, syn) = performance_mark_syn(ctx, b);
      let (t_side, m) = matched_proj_typ(prod_side, syn);
      (Proj(prod_side, e, m), t_side);
    }
  | Asc(e, t) => (Asc(performance_mark_ana(ctx, t, e), t), t)
  | Nil => (Nil, List)
  | Cons => (Cons, Arrow(Num, Arrow(List, List)))
  | ListRec(t) => (
      ListRec(t),
      Arrow(t, Arrow(Arrow(Num, Arrow(t, t)), Arrow(List, t))),
    )
  | Y(t) => (Y(t), Arrow(Arrow(Arrow(t, t), Arrow(t, t)), Arrow(t, t)))
  | ITE(t) => (
      ListRec(t),
      Arrow(Bool, Arrow(Arrow(Unit, t), Arrow(Arrow(Unit, t), t))),
    )
  | EHole => (EHole, Hole)

and performance_mark_ana = (ctx: Ctx.t, ana: Htyp.t): (bareExp => markedExp) =>
  fun
  | Lam(x, t, e) => {
      let (t1, t2, m1) = matched_arrow_typ(ana);
      let m2 = type_consistent(t, t1);
      Ctx.extend_bind(ctx, x, t);
      let body = performance_mark_ana(ctx, t2, e);
      Ctx.remove_bind(ctx, x);
      Lam(x, t, m1, m2, body);
    }
  | Pair(b1, b2) => {
      let (t1, t2, m) = matched_product_typ(ana);
      let e1 = performance_mark_ana(ctx, t1, b1);
      let e2 = performance_mark_ana(ctx, t2, b2);
      Pair(e1, e2, m);
    }
  | b => {
      let (e, syn) = performance_mark_syn(ctx, b);
      let m = type_consistent(syn, ana);
      Subsume(e, m);
    };

let performance_mark = (e: bareExp) => {
  let _ = performance_mark_syn(Ctx.empty, e);
  ();
};

let dummy_interval = () => {
  let a = Order.create();
  let b = Order.add_next(a);
  (a, b);
};

let wrap_upper = (m: Iexp.middle, syn: option(Htyp.t)): Iexp.upper => {
  parent: Deleted,
  syn,
  middle: m,
  interval: dummy_interval(),
  in_queue_upper: InQueue.default_upper(),
  deleted_upper: false,
};

let wrap_lower =
    (e: Iexp.upper, marked: Mark.t, ana: option(Htyp.t)): Iexp.lower => {
  upper: dummy_upper(),
  ana,
  marked,
  child: e,
  in_queue_lower: InQueue.default_lower(),
  deleted_lower: false,
};

// this is not gonna set the binding or interval fields. it suffices to check
// our incremental computation against the visible data, i.e. marks.
// it also will not set parent or skip up pointers. we just need to walk down.
let rec validity_mark_syn = (ctx: Ctx.t): (bareExp => Iexp.upper) =>
  fun
  | Var(x) => {
      let (t, m) = Ctx.lookup(ctx, x);
      wrap_upper(Var(x, ref(m), ref(Iexp.Deleted)), Some(t));
    }
  | NumLit(x) => wrap_upper(NumLit(x), Some(Num))
  | Plus(e1, e2) =>
    wrap_upper(
      Plus(
        validity_mark_ana(ctx, Num, e1),
        validity_mark_ana(ctx, Num, e2),
      ),
      Some(Num),
    )
  | Lam(x, t, e) => {
      Ctx.extend_bind(ctx, x, t);
      let body = validity_mark_syn(ctx, e);
      Ctx.remove_bind(ctx, x);
      let syn = Option.get(body.syn);
      wrap_upper(
        Lam(
          ref(x),
          ref(t),
          ref(Mark.Unmarked),
          ref(Mark.Unmarked),
          wrap_lower(body, Unmarked, None),
          ref(Tree.empty),
        ),
        Some(Arrow(t, syn)),
      );
    }
  | Ap(b1, b2) => {
      let e1 = validity_mark_syn(ctx, b1);
      let syn = Option.get(e1.syn);
      let (t1, t2, m) = matched_arrow_typ(syn);
      let e2 = validity_mark_ana(ctx, t1, b2);
      wrap_upper(
        Ap(wrap_lower(e1, Unmarked, None), ref(m), e2),
        Some(t2),
      );
    }
  | Pair(b1, b2) => {
      let e1 = validity_mark_syn(ctx, b1);
      let e2 = validity_mark_syn(ctx, b2);
      let syn1 = Option.get(e1.syn);
      let syn2 = Option.get(e2.syn);
      wrap_upper(
        Pair(
          wrap_lower(e1, Unmarked, None),
          wrap_lower(e2, Unmarked, None),
          ref(Mark.Unmarked),
        ),
        Some(Product(syn1, syn2)),
      );
    }
  | Proj(prod_side, b) => {
      let e = validity_mark_syn(ctx, b);
      let syn = Option.get(e.syn);
      let (t_side, m) = matched_proj_typ(prod_side, syn);
      wrap_upper(
        Proj(prod_side, wrap_lower(e, Unmarked, None), ref(m)),
        Some(t_side),
      );
    }
  | Asc(e, t) =>
    wrap_upper(Asc(validity_mark_ana(ctx, t, e), ref(t)), Some(t))
  | Nil => wrap_upper(Nil, Some(List))
  | Cons => wrap_upper(Cons, Some(Arrow(Num, Arrow(List, List))))
  | ListRec(t) =>
    wrap_upper(
      ListRec(ref(t)),
      Some(Arrow(t, Arrow(Arrow(Num, Arrow(t, t)), Arrow(List, t)))),
    )
  | Y(t) =>
    wrap_upper(
      Y(ref(t)),
      Some(Arrow(Arrow(Arrow(t, t), Arrow(t, t)), Arrow(t, t))),
    )
  | ITE(t) =>
    wrap_upper(
      ListRec(ref(t)),
      Some(Arrow(Bool, Arrow(Arrow(Unit, t), Arrow(Arrow(Unit, t), t)))),
    )
  | EHole => wrap_upper(EHole, Some(Hole))

and validity_mark_ana = (ctx: Ctx.t, ana: Htyp.t): (bareExp => Iexp.lower) =>
  fun
  | Lam(x, t, e) => {
      let (t1, t2, m1) = matched_arrow_typ(ana);
      let m2 = type_consistent(t, t1);
      Ctx.extend_bind(ctx, x, t);
      let body = validity_mark_ana(ctx, t2, e);
      Ctx.remove_bind(ctx, x);
      let middle: Iexp.middle =
        Lam(ref(x), ref(t), ref(m1), ref(m2), body, ref(Tree.empty));
      wrap_lower(wrap_upper(middle, None), Unmarked, Some(ana));
    }
  | Pair(b1, b2) => {
      let (t1, t2, m) = matched_product_typ(ana);
      let e1 = validity_mark_ana(ctx, t1, b1);
      let e2 = validity_mark_ana(ctx, t2, b2);
      let middle: Iexp.middle = Pair(e1, e2, ref(m));
      wrap_lower(wrap_upper(middle, None), Unmarked, Some(ana));
    }
  | b => {
      let e = validity_mark_syn(ctx, b);
      let syn = Option.get(e.syn);
      let m = type_consistent(syn, ana);
      wrap_lower(e, m, Some(ana));
    };

let remark = (e: Iexp.upper) =>
  validity_mark_syn(Ctx.empty, erase_upper(e));

let rec equiv_upper = (e1: Iexp.upper, e2: Iexp.upper): bool =>
  e1.syn == e2.syn && equiv_middle(e1.middle, e2.middle)

and equiv_middle = (e1: Iexp.middle, e2: Iexp.middle): bool => {
  let return = b => b;
  // { b ? b : { print_endline("inequiv!"); b }; };
  switch (e1, e2) {
  | (Var(x1, m1, _), Var(x2, m2, _)) =>
    //print_endine("comparing var");
    return((x1, m1) == (x2, m2))
  | (NumLit(x1), NumLit(x2)) =>
    //print_endine("comparing numlit");
    return(x1 == x2)
  | (Plus(e1, e2), Plus(e3, e4)) =>
    //print_endine("comparing plus");
    return(equiv_lower(e1, e3) && equiv_lower(e2, e4))
  | (Lam(x1, t1, m1, m2, e1, _), Lam(x2, t2, m3, m4, e2, _)) =>
    //print_endine("comparing lam");
    return((x1, t1, m1, m2) == (x2, t2, m3, m4) && equiv_lower(e1, e2))
  | (Ap(e1, m1, e2), Ap(e3, m2, e4)) =>
    //print_endine("comparing ap");
    return(equiv_lower(e1, e3) && m1 == m2 && equiv_lower(e2, e4))
  | (Pair(e1, e2, m1), Pair(e3, e4, m2)) =>
    return(equiv_lower(e1, e3) && equiv_lower(e2, e4)) && m1 == m2
  | (Proj(s1, e1, m1), Proj(s2, e2, m2)) =>
    return(equiv_lower(e1, e2) && s1 == s2 && m1 == m2)
  | (Asc(e1, t1), Asc(e2, t2)) =>
    //print_endine("comparing asc");
    equiv_lower(e1, e2) && t1 == t2
  | (EHole, EHole) => true
  | (Nil, Nil) => true
  | (Cons, Cons) => true
  | (ListRec(t1), ListRec(t2)) => t1 == t2
  | (Y(t1), Y(t2)) => t1 == t2
  | _ => false
  };
}

and equiv_lower = (e1: Iexp.lower, e2: Iexp.lower): bool =>
  e1.ana == e2.ana
  && e1.marked == e2.marked
  && equiv_upper(e1.child, e2.child);

let marked_correctly = e => {
  let e' = remark(e);
  equiv_upper(e, e') ? None : Some(e');
};
