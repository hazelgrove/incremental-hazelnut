open Hazelnut;
open Incremental;
open Order;
open Tree;
// open Hashtbl;

type bareExp =
  | Var(string)
  | NumLit(int)
  | Plus(bareExp, bareExp)
  | Lam(Bind.t, Htyp.t, bareExp)
  | Ap(bareExp, bareExp)
  | Asc(bareExp, Htyp.t)
  | EHole;

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
  | Asc(e, t) => Asc(erase_lower(e), t.contents)
  | EHole => EHole

and erase_upper = (e: Iexp.upper): bareExp => {
  erase_middle(e.middle);
};

let dummy_interval = (Order.null, Order.null);

let wrap_upper = (m: Iexp.middle, syn: option(Htyp.t)): Iexp.upper => {
  parent: Deleted,
  syn,
  middle: m,
  interval: dummy_interval,
  in_queue_upper: InQueue.default_upper(),
  deleted_upper: false,
};

let wrap_lower =
    (e: Iexp.upper, marked: Mark.t, ana: option(Htyp.t)): Iexp.lower => {
  upper: dummy_upper,
  ana,
  marked,
  child: e,
  in_queue_lower: InQueue.default_lower(),
  deleted_lower: false,
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

// this is not gonna set the binding or interval fields. it suffices to check
// our incremental computation against the visible data, i.e. marks.
// it also will not set parent or skip up pointers. we just need to walk down.
let rec mark_syn = (ctx: Ctx.t): (bareExp => Iexp.upper) =>
  fun
  | Var(x) => {
      let (t, m) = Ctx.lookup(ctx, x);
      wrap_upper(Var(x, ref(m), ref(Iexp.Deleted)), Some(t));
    }
  | NumLit(x) => wrap_upper(NumLit(x), Some(Num))
  | Plus(e1, e2) =>
    wrap_upper(
      Plus(mark_ana(ctx, Num, e1), mark_ana(ctx, Num, e2)),
      Some(Num),
    )
  | Lam(x, t, e) => {
      Ctx.extend_bind(ctx, x, t);
      let body = mark_syn(ctx, e);
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
      let e1 = mark_syn(ctx, b1);
      let syn = Option.get(e1.syn);
      let (t1, t2, m) = matched_arrow_typ(syn);
      let e2 = mark_ana(ctx, t1, b2);
      wrap_upper(
        Ap(wrap_lower(e1, Unmarked, None), ref(m), e2),
        Some(t2),
      );
    }
  | Asc(e, t) => wrap_upper(Asc(mark_ana(ctx, t, e), ref(t)), Some(t))
  | EHole => wrap_upper(EHole, Some(Hole))

and mark_ana = (ctx: Ctx.t, ana: Htyp.t): (bareExp => Iexp.lower) =>
  fun
  | Lam(x, t, e) => {
      let (t1, t2, m1) = matched_arrow_typ(ana);
      let m2 = type_consistent(t, t1);
      Ctx.extend_bind(ctx, x, t);
      let body = mark_ana(ctx, t2, e);
      Ctx.remove_bind(ctx, x);
      let middle: Iexp.middle =
        Lam(ref(x), ref(t), ref(m1), ref(m2), body, ref(Tree.empty));
      wrap_lower(wrap_upper(middle, None), Unmarked, Some(ana));
    }
  | b => {
      let e = mark_syn(ctx, b);
      let syn = Option.get(e.syn);
      let m = type_consistent(syn, ana);
      wrap_lower(e, m, Some(ana));
    };

let remark = (e: Iexp.upper) => mark_syn(Ctx.empty, erase_upper(e));

let rec equiv_upper = (e1: Iexp.upper, e2: Iexp.upper): bool =>
  e1.syn == e2.syn && equiv_middle(e1.middle, e2.middle)

and equiv_middle = (e1: Iexp.middle, e2: Iexp.middle): bool => {
  let return = b => {
    b
      ? b
      : {
        //print_endine("inequiv!");
        b;
      };
  };
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
  | (Asc(e1, t1), Asc(e2, t2)) =>
    //print_endine("comparing asc");
    equiv_lower(e1, e2) && t1 == t2
  | (EHole, EHole) => true
  | _ => false
  };
}

and equiv_lower = (e1: Iexp.lower, e2: Iexp.lower): bool =>
  e1.ana == e2.ana
  && e1.marked == e2.marked
  && equiv_upper(e1.child, e2.child);

let marked_correctly = e =>
  equiv_upper(e, remark(e)) ? None : Some(remark(e));
