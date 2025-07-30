open Sys;
open Yojson;
open Unix;
open Core;
open PPrint;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Hazelnut;
open Hazelnut_lib.Incremental;
open Hazelnut_lib.State;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Actions_random;
open Hazelnut_lib.UpdateProcess;
open Hazelnut_lib.Marking;
open Ocaml_intrinsics;
open Gc;

let _ = Gc.set({...Gc.get(), space_overhead: 1200});

let random_element = x => List.nth_exn(x, Random.int(List.length(x)));

let () = assert(Array.length(Sys.argv) == 2);

let file_path = "log/" ++ Sys.argv[1];

let () = print_endline("writing to file " ++ file_path);

let shell = cmd => {
  let in_channel = Core_unix.open_process_in(cmd);
  In_channel.iter_lines(in_channel, ~f=str => print_endline(str));
  let res = Core_unix.close_process_in(in_channel);
  switch (res) {
  | Ok () => ()
  | _ => failwith("shell failed")
  };
};

let () = shell("mkdir -p log/");
let () = shell("touch " ++ file_path);

let c = Stdio.Out_channel.create(file_path);

let timed = (f: unit => 'a) => {
  let before = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  let result = f();
  let after = Stdlib.Int64.to_int(Ocaml_intrinsics.Perfmon.rdtsc());
  (after - before, result);
};

type exp =
  | [@deriving sexp] Hole
  | Lit(int)
  | Var(string)
  | Let(exp, exp, exp)
  | Lam(exp, exp, exp)
  | Zro(exp)
  | Fst(exp)
  | Tup(exp, exp)
  | Prod(exp, exp)
  | Arrow(exp, exp)
  | List
  | Unit
  | Int
  | Lt
  | Nil
  | Cons
  | /** List -> 'a -> (Num -> List -> 'a) -> 'a */
    ListMatch(exp)
  | /** 'a -> (Num -> 'a -> 'a) -> List -> 'a */
    ListRec(exp)
  | /** (('a -> 'a) -> ('a -> 'a)) -> ('a -> 'a) */
    Y(exp)
  | ITE(exp)
  | App(exp, exp);

// should only be one level deep - an node where all children is Hole
type hexp = exp;

type action =
  | Down(int)
  // S for silent
  | SDown(int)
  | Up
  | SUp
  | Delete
  | Replace(hexp)
  | ReplaceDown(int)
  | ReplaceUp(hexp, int)
  | AssertRoot;

let app2 = (f: exp, a: exp, b: exp) => App(App(f, a), b);

let app3 = (f: exp, a: exp, b: exp, c: exp) => App(app2(f, a, b), c);

let const = (x: exp) => Lam(Var("_"), Unit, x);

let lam2 = (x: exp, xt: exp, y: exp, yt: exp, b: exp) =>
  Lam(x, xt, Lam(y, yt, b));

let ite = (ty, i, t, e) => app3(ITE(ty), i, const(t), const(e));

let list_rec =
    (
      t: exp,
      base_case: exp,
      cons_x_name: exp,
      cons_xs_name: exp,
      cons_case: exp,
      list: exp,
    ) =>
  app3(
    ListRec(t),
    base_case,
    lam2(cons_x_name, Int, cons_xs_name, t, cons_case),
    list,
  );

let list_match =
    (
      t: exp,
      list: exp,
      base_case: exp,
      cons_x_name: exp,
      cons_xs_name: exp,
      cons_case: exp,
    ) =>
  app3(
    ListMatch(t),
    list,
    base_case,
    lam2(cons_x_name, Int, cons_xs_name, List, cons_case),
  );

let y = (t: exp, self: exp, impl: exp) => App(Y(t), Lam(self, t, impl));
let cons = (x: exp, xs: exp) => app2(Cons, x, xs);

let let_ = (lhs, ty, rhs, body) => App(Lam(lhs, ty, body), rhs);

let merge =
  y(
    Arrow(List, Arrow(List, List)),
    Var("merge"),
    lam2(
      Var("xs"),
      List,
      Var("ys"),
      List,
      list_match(
        List,
        Var("xs"),
        Var("ys"),
        Var("x"),
        Var("xs"),
        list_match(
          List,
          Var("ys"),
          cons(Var("x"), Var("xs")),
          Var("y"),
          Var("ys"),
          ite(
            List,
            app2(Lt, Var("x"), Var("y")),
            cons(
              Var("x"),
              app2(Var("merge"), Var("xs"), cons(Var("y"), Var("ys"))),
            ),
            cons(
              Var("y"),
              app2(Var("merge"), cons(Var("x"), Var("xs")), Var("ys")),
            ),
          ),
        ),
      ),
    ),
  );
/**fun (xs:[Int], ys:[Int]) ->
  case xs
    | [] => ys
    | x::xs =>
    case ys
      | [] => x::xs
      | y::ys => if x < y then x :: merge(xs, y::ys) else y :: merge(x::xs, ys)
    end
  end */
let split =
  Lam(
    Var("xs"),
    List,
    list_rec(
      Prod(List, List),
      Tup(Nil, Nil),
      Var("x"),
      Var("yszs"),
      Tup(cons(Var("x"), Fst(Var("yszs"))), Zro(Var("yszs"))),
      Var("xs"),
    ),
  );
/**split : [Int] -> ([Int], [Int]) =
  fun xs ->
    case xs
      | [] => ([], [])
      | x::xs =>
      let (ys, zs) = split(xs) in
      (x::zs, ys)
    end */
let mergesort = (merge, split) =>
  y(
    Arrow(List, List),
    Var("mergesort"),
    Lam(
      Var("xs"),
      List,
      list_match(
        List,
        Var("xs"),
        Nil,
        Var("x"),
        Var("xs"),
        list_match(
          List,
          Var("xs"),
          cons(Var("xs"), Nil),
          Var("_"),
          Var("_"),
          let_(
            Var("yszs"),
            Tup(List, List),
            App(split, Var("xs")),
            let_(
              Var("ys"),
              List,
              Zro(Var("yszs")),
              let_(
                Var("zs"),
                List,
                Fst(Var("yszs")),
                let_(
                  Var("ys"),
                  List,
                  App(Var("mergesort"), Var("ys")),
                  let_(
                    Var("zs"),
                    List,
                    App(Var("mergesort"), Var("zs")),
                    App(merge, Tup(Var("ys"), Var("zs"))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    ),
  );
/**mergesort : [Int] -> [Int] =
  fun xs ->
    case xs
      | [] => []
      | [x] => [x]
      | _ =>
      let (ys, zs) = split(xs) in
      let ys = mergesort(ys) in
      let zs = mergesort(zs) in
      merge(ys, zs)
    end */

let program =
  Let(
    Var("merge"),
    merge,
    Let(
      Var("split"),
      split,
      Let(
        Var("mergesort"),
        mergesort(Var("merge"), Var("split")),
        Var("mergesort"),
      ),
    ),
  );

let rec overlapping_mergesort = (n: int, bound) => {
  let_(
    Var("merge" ++ string_of_int(n)),
    Arrow(List, Arrow(List, List)),
    merge,
    let_(
      Var("split" ++ string_of_int(n)),
      Arrow(List, Tup(List, List)),
      split,
      let_(
        Var("mergesort"),
        Arrow(List, List),
        mergesort(
          Var("merge" ++ string_of_int(Random.int(n + 1))),
          Var("split" ++ string_of_int(Random.int(n + 1))),
        ),
        if (n >= bound) {
          Var("mergesort");
        } else {
          overlapping_mergesort(n + 1, bound);
        },
      ),
    ),
  );
};

let rec case_name = (x: exp): string =>
  switch (x) {
  | Hole => "Hole"
  | Var(v) => "Var"
  | App(f, xs) => "App"
  | Let(lhs, rhs, body) => "Let"
  | ListMatch(_) => "ListMatch"
  | Tup(x, y) => "Tup"
  | Lit(i) => "Lit"
  | Lam(arg_name, arg_type, body) => "Lam"
  | List => "List"
  | Prod(x, y) => "Prod"
  | Int => "Int"
  | Zro(x) => "Zro"
  | Fst(x) => "Fst"
  | Nil => "Nil"
  | Cons => "Cons"
  | ITE(t) => "Ite"
  | Lt => "Lt"
  | Arrow(_, _) => "Arrow"
  | Unit => "Unit"
  | ListRec(_) => "ListRec"
  | Y(_) => "Y"
  };

let rec pprint = (x: exp): PPrint.document =>
  switch (x) {
  | Hole => string("HOLE")
  | Var(v) => string(v)
  | App(f, xs) => pprint(f) ^^ string("(") ^^ pprint(xs) ^^ string(")")
  | Let(lhs, rhs, body) =>
    string("let ")
    ^^ pprint(lhs)
    ^^ string(" = ")
    ^^ pprint(rhs)
    ^^ string(" in")
    ^^ group(break(1) ^^ pprint(body))
  | ListMatch(ty) => string("ListMatch @") ^^ pprint(ty)
  | Tup(x, y) =>
    string("(") ^^ pprint(x) ^^ string(", ") ^^ pprint(y) ^^ string(")")
  | Arrow(x, y) =>
    string("(") ^^ pprint(x) ^^ string(" -> ") ^^ pprint(y) ^^ string(")")
  | Lit(i) => string(string_of_int(i))
  | Lam(arg_name, arg_type, body) =>
    string("fun ")
    ^^ pprint(arg_name)
    ^^ string(": ")
    ^^ pprint(arg_type)
    ^^ string(" -> ")
    ^^ pprint(body)
  | List => string("[") ^^ string("int") ^^ string("]")
  | Prod(x, y) => pprint(x) ^^ string(" * ") ^^ pprint(y)
  | Int => string("int")
  | Zro(x) => pprint(x) ^^ string(".0")
  | Fst(x) => pprint(x) ^^ string(".1")
  | Nil => string("[]@int")
  | Cons => string("Cons")
  | ITE(ty) => string("ITE @") ^^ pprint(ty)
  | ListRec(ty) => string("ListRec @") ^^ pprint(ty)
  | Lt => string("Lt")
  | Unit => string("Unit")
  | Y(ty) => string("Y @") ^^ pprint(ty)
  | _ =>
    print_endline(case_name(x));
    failwith("pprint");
  };

let rec pprint_action = (x: action): PPrint.document =>
  switch (x) {
  | Down(i) => string("Down " ++ string_of_int(i))
  | SDown(i) => string("SDown " ++ string_of_int(i))
  | Up => string("Up")
  | SUp => string("SUp")
  | Replace(x) => string("Replace ") ^^ pprint(x)
  | ReplaceDown(i) => string("ReplaceDown " ++ string_of_int(i))
  | Delete => string("Delete")
  | AssertRoot => string("AssertRoot")
  | ReplaceUp(x, i) =>
    string("ReplaceUp ") ^^ pprint(x) ^^ string(" " ++ string_of_int(i))
  };

let pretty_print = x => {
  PPrint.ToChannel.pretty(0.8, 160, Stdio.Out_channel.stdout, pprint(x));
  print_endline("");
};

let pretty_print_action = x => {
  PPrint.ToChannel.pretty(
    0.8,
    160,
    Stdio.Out_channel.stdout,
    pprint_action(x),
  );
  print_endline("");
};

type splitted =
  | Binder(string)
  | Type(exp)
  | Term(exp);
type anal_t = {
  path: List.t(int),
  ctx: List.t(string),
  term: splitted,
};
let anal_here = x => {path: [], ctx: [], term: x};
let extend_anal = (loc, ctx, anal) => {
  path: [loc] @ anal.path,
  ctx: ctx @ anal.ctx,
  term: anal.term,
};
let rec analysis = (x: exp) => {
  switch (x) {
  | Nil
  | Cons
  | Lt
  | Var(_) => [anal_here(Term(x))]
  | Int
  | List
  | Unit => [anal_here(Type(x))]
  | Fst(a)
  | Zro(a)
  | Y(a)
  | ListMatch(a)
  | ListRec(a)
  | ITE(a) =>
    [anal_here(Term(x))] @ List.map(analysis(a), extend_anal(0, []))
  | Tup(a, b)
  | App(a, b) =>
    [anal_here(Term(x))]
    @ List.map(analysis(a), extend_anal(0, []))
    @ List.map(analysis(b), extend_anal(1, []))
  | Prod(a, b)
  | Arrow(a, b) =>
    [anal_here(Type(x))]
    @ List.map(analysis(a), extend_anal(0, []))
    @ List.map(analysis(b), extend_anal(1, []))
  | Lam(Var(a), b, c) =>
    [anal_here(Term(x)), extend_anal(0, [], anal_here(Binder(a)))]
    @ List.map(analysis(b), extend_anal(1, []))
    @ List.map(analysis(c), extend_anal(2, [a]))
  | _ =>
    pretty_print(x);
    failwith("analysis");
  };
};
let program = overlapping_mergesort(0, 100);
let anal = analysis(program);

type context = list(exp => exp);

let go_down = (x: exp, ctx: context, i: int): (exp, context) =>
  switch (x) {
  | Let(lhs, rhs, body) =>
    if (i == 0) {
      (lhs, [(x => Let(x, rhs, body)), ...ctx]);
    } else if (i == 1) {
      (rhs, [(x => Let(lhs, x, body)), ...ctx]);
    } else if (i == 2) {
      (body, [(x => Let(lhs, rhs, x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ITE(ty) =>
    if (i == 0) {
      (ty, [(x => ITE(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ListRec(ty) =>
    if (i == 0) {
      (ty, [(x => ListRec(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Lam(arg_name, arg_type, body) =>
    if (i == 0) {
      (arg_name, [(x => Lam(x, arg_type, body)), ...ctx]);
    } else if (i == 1) {
      (arg_type, [(x => Lam(arg_name, x, body)), ...ctx]);
    } else if (i == 2) {
      (body, [(x => Lam(arg_name, arg_type, x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | ListMatch(ty) =>
    if (i == 0) {
      (ty, [(x => ListMatch(ty)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Zro(x) =>
    if (i == 0) {
      (x, [(x => Zro(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Fst(x) =>
    if (i == 0) {
      (x, [(x => Zro(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Prod(x, y) =>
    if (i == 0) {
      (x, [(x => Prod(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Prod(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Arrow(x, y) =>
    if (i == 0) {
      (x, [(x => Arrow(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Arrow(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | App(x, y) =>
    if (i == 0) {
      (x, [(x => App(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => App(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Tup(x, y) =>
    if (i == 0) {
      (x, [(x => Tup(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Tup(x, y)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Y(x) =>
    if (i == 0) {
      (x, [(x => Y(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | _ =>
    pretty_print(x);
    failwith("go_down");
  };
let replace_down = (x: exp, ctx: context, i: int): (exp, context) => {
  let (x', _) = go_down(x, ctx, i);
  (x', ctx);
};

let go_up = (x: exp, ctx: context): (exp, context) =>
  switch (ctx) {
  | [c, ...ctx] => (c(x), ctx)
  };

let replace_up = (h: exp, x: exp, ctx: context, i): (exp, context) => {
  let (_, [ctx']) = go_down(h, [], i);
  (ctx'(x), ctx);
};
let rec uppest = (x: exp, ctx: context) =>
  switch (ctx) {
  | [] => x
  | [c, ...ctx] => uppest(c(x), ctx)
  };

let step_trace = ((x: exp, ctx: context), act: action): (exp, context) => {
  switch (act) {
  | Down(i)
  | SDown(i) => go_down(x, ctx, i)
  | Up
  | SUp => go_up(x, ctx)
  | ReplaceDown(i) => replace_down(x, ctx, i)
  | ReplaceUp(h, i) => replace_up(h, x, ctx, i)
  | Replace(x) => (x, ctx)
  | Delete => (Hole, ctx)
  | AssertRoot =>
    assert(List.is_empty(ctx));
    (x, ctx);
  };
};

let rec apply_traces = ((x: exp, ctx: context), act) => {
  if (false && List.length(ctx) % 10 == 0) {
    pretty_print(uppest(x, ctx));
  };
  switch (act) {
  | [] => (x, ctx)
  | [act, ...acts] =>
    let (x, ctx) = step_trace((x, ctx), act);
    apply_traces((x, ctx), acts);
  };
};

let anal_touch = (anal: anal_t) => {
  let ret =
    List.map(anal.path, i => SDown(i))
    @ (
      switch (anal.term) {
      | Binder(x) => [
          Delete,
          Replace(Var(random_element([x] @ anal.ctx))),
          Delete,
          Replace(Var(x)),
        ]
      | Type(x) =>
        switch (x) {
        | List
        | Int
        | Unit => [Delete, Replace(Unit), Delete, Replace(x)]
        | Prod(_, _)
        | Arrow(_, _) => [ReplaceUp(Prod(Hole, Hole), 0), ReplaceDown(0)]
        | _ =>
          pretty_print(x);
          failwith("anal type");
        }
      | Term(x) =>
        switch (x) {
        | Cons
        | Nil
        | Lt
        | Var(_) => [
            Delete,
            Replace(
              random_element([Lit(0)] @ List.map(anal.ctx, v => Var(v))),
            ),
            Delete,
            Replace(x),
          ]
        | ListMatch(_)
        | ListRec(_)
        | Y(_)
        | ITE(_)
        | App(_, _)
        | Lam(_, _, _)
        | Tup(_, _) => [ReplaceUp(Tup(Hole, Hole), 0), ReplaceDown(0)]
        | Zro(_) => [ReplaceDown(0), ReplaceUp(Zro(Hole), 0)]
        | Fst(_) => [ReplaceDown(0), ReplaceUp(Fst(Hole), 0)]
        | _ =>
          pretty_print(x);
          failwith("anal term");
        }
      }
    )
    @ List.map(anal.path, _ => SUp)
    @ [AssertRoot];
  let (_, []) = apply_traces((program, []), ret);
  ret;
};

let shuffle = d => {
  let nd = List.map(d, c => (Random.bits(), c));
  let sond = List.sort(nd, (x, y) => compare(fst(x), fst(y)));
  List.map(sond, snd);
};

let rec subedits = (x: exp, loc: int) => {
  [Down(loc)] @ edits(x) @ [Up];
}
and edits = (x: exp) => {
  switch (x) {
  | ListMatch(x) =>
    [Replace(ListMatch(Hole))] @ List.join(shuffle([subedits(x, 0)]))
  | Let(lhs, rhs, body) =>
    [Replace(Let(Hole, Hole, Hole))]
    @ List.join(
        shuffle([subedits(lhs, 0), subedits(rhs, 1), subedits(body, 2)]),
      )
  | Lam(arg_name, arg_type, body) =>
    [Replace(Lam(Hole, Hole, Hole))]
    @ List.join(
        shuffle([
          subedits(arg_name, 0),
          subedits(arg_type, 1),
          subedits(body, 2),
        ]),
      )
  | ITE(ty) =>
    [Replace(ITE(Hole))] @ List.join(shuffle([subedits(ty, 0)]))
  | ListRec(ty) =>
    [Replace(ListRec(Hole))] @ List.join(shuffle([subedits(ty, 0)]))
  | App(f, xs) =>
    [Replace(App(Hole, Hole))]
    @ List.join(shuffle([subedits(f, 0), subedits(xs, 1)]))
  | Arrow(x, y) =>
    [Replace(Arrow(Hole, Hole))]
    @ List.join(shuffle([subedits(x, 0), subedits(y, 1)]))
  | Tup(l, r) =>
    [Replace(Tup(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Prod(l, r) =>
    [Replace(Prod(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Zro(x) => [Replace(Zro(Hole))] @ subedits(x, 0)
  | Fst(x) => [Replace(Fst(Hole))] @ subedits(x, 0)
  | Y(x) => [Replace(Y(Hole))] @ subedits(x, 0)
  | Nil
  | Unit
  | Lt
  | Cons
  | List
  | Var(_)
  | Int => [Replace(x)]
  | _ =>
    pretty_print(x);
    failwith("edits");
  };
};

let rec atomic_type = (x: exp) => {
  switch (x) {
  | App(_, _)
  | Lam(_, _, _)
  | Arrow(_, _)
  | Var(_)
  | Prod(_, _)
  | Tup(_, _)
  | Nil
  | Cons
  | Zro(_)
  | Fst(_)
  | ListRec(_)
  | ListMatch(_)
  | Y(_) => false
  | Int
  | List => true
  | _ =>
    pretty_print(x);
    failwith("atomic_type");
  };
};

let rec atomic_term = (x: exp) => {
  switch (x) {
  | App(_, _)
  | Lam(_, _, _)
  | Arrow(_, _)
  | Prod(_, _)
  | Tup(_, _)
  | Zro(_)
  | Fst(_)
  | ListRec(_)
  | ListMatch(_)
  | Y(_) => false
  | Nil
  | Cons
  | Var(_) => true
  | _ =>
    pretty_print(x);
    failwith("atomic_term");
  };
};

let rec children = (x: exp) => {
  switch (x) {
  | ListRec(a)
  | ListMatch(a)
  | Zro(a)
  | Y(a) => [(0, a)]
  | Tup(a, b)
  | Prod(a, b)
  | App(a, b)
  | Arrow(a, b) => [(0, a), (1, b)]
  | Lam(_, t, b) => [(1, t), (2, b)]
  | _ =>
    pretty_print(x);
    failwith("children");
  };
};
let rec touch = (x: exp) =>
  if (atomic_type(x)) {
    [Delete, Replace(Unit), Delete, Replace(x)];
  } else if (atomic_term(x)) {
    [Delete, Replace(Lit(0)), Delete, Replace(x)];
  } else {
    let c = children(x);
    let (i, x) = List.nth_exn(c, Random.int(List.length(c)));
    [Down(i)] @ touch(x) @ [Up];
  };

let wrap_insert = [
  ReplaceUp(Lam(Hole, Hole, Hole), 2),
  Down(0),
  Replace(Var("x")),
  Up,
  Down(1),
  Replace(Int),
  Up,
];
let wrap_delete = [ReplaceDown(0)];
let wrap_amount = 5000;
/*let trace =
  List.join(
    List.init(wrap_amount, (f) =>
      (
        {
          wrap_insert;
        }: _
      )
    ),
  );*/
// List.join(
//   List.init(wrap_amount, (f) =>
//     (
//       {
//         edits(program);
//       }: _
//     )
//   ),
// );
// );
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program)
// @ edits(program);
// @ List.join(
//     List.init(wrap_amount, (f) =>
//       (
//         {
//           wrap_delete;
//         }: _
//       )
//     ),
//   );

let trace =
  edits(program)
  @ [AssertRoot]
  @ List.join(
      List.init(500, _ =>
        anal_touch(List.nth_exn(anal, Random.int(List.length(anal))))
      ),
    );

// apply_traces(Hole, [], trace);

let wrap: list(Iaction.t) = [
  WrapPlus(Two),
  WrapLam,
  MoveDown(One),
  InsertVar("x"),
  MoveUp,
  MoveDown(Two),
  WrapArrow(One),
  MoveDown(One),
  InsertNumType,
  MoveUp,
  MoveUp,
];

let wraps =
  wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap @ wrap;

let wraps = wraps @ wraps @ wraps @ wraps @ wraps @ wraps @ wraps @ wraps;
// let wraps = wraps @ wraps @ wraps @ wraps;

// let actions: list(Iaction.t) = [Iaction.InsertVar("x")] @ wraps;

// let actions = List.concat(random_action_segments(10000));

let to_iaction = (act: action) => {
  switch (act) {
  | Up
  | SUp => [Iaction.MoveUp]
  | Down(0)
  | SDown(0) => [Iaction.MoveDown(One)]
  | Down(1)
  | SDown(1) => [Iaction.MoveDown(Two)]
  | Down(2)
  | SDown(2) => [Iaction.MoveDown(Three)]
  | ReplaceUp(Lam(Hole, Hole, Hole), 2) => [Iaction.WrapLam]
  | ReplaceUp(Tup(Hole, Hole), 0) => [Iaction.WrapPair(One)]
  | ReplaceUp(Prod(Hole, Hole), 0) => [Iaction.WrapProduct(One)]
  | ReplaceUp(Zro(Hole), 0) => [
      Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Fst),
    ]
  | ReplaceUp(Fst(Hole), 0) => [
      Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Snd),
    ]
  | Replace(Arrow(Hole, Hole)) => [Iaction.WrapArrow(One)]
  | Replace(Prod(Hole, Hole)) => [Iaction.WrapProduct(One)]
  | Replace(Tup(Hole, Hole)) => [Iaction.WrapPair(One)]
  | Replace(Lam(Hole, Hole, Hole)) => [Iaction.WrapLam]
  | Replace(App(Hole, Hole)) => [Iaction.WrapAp(One)]
  | Replace(Zro(Hole)) => [
      Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Fst),
    ]
  | Replace(Fst(Hole)) => [
      Iaction.WrapProj(Hazelnut_lib.Hazelnut.ProdSide.Snd),
    ]
  | Replace(ListRec(Hole)) => [Iaction.InsertListRec]
  | Replace(Y(Hole)) => [Iaction.InsertY]
  | Replace(ITE(Hole)) => [Iaction.InsertITE]
  | Replace(ListMatch(Hole)) => [Iaction.InsertListMatch]
  | Replace(Nil) => [Iaction.InsertNil]
  | Replace(Lt) => [Iaction.InsertLt]
  | Replace(Cons) => [Iaction.InsertCons]
  | Replace(Var(x)) => [Iaction.InsertVar(x)]
  | Replace(Lit(x)) => [Iaction.InsertNumLit(x)]
  | Replace(Int) => [Iaction.InsertNumType]
  | Replace(List) => [Iaction.InsertList]
  | Replace(Unit) => [Iaction.InsertUnitType]
  | ReplaceDown(0) => [Iaction.Unwrap(One)]
  | ReplaceDown(1) => [Iaction.Unwrap(Two)]
  | ReplaceDown(2) => [Iaction.Unwrap(Three)]
  | Delete => [Iaction.Delete]
  | AssertRoot => []
  | _ =>
    pretty_print_action(act);
    failwith("to_iaction");
  };
};

type eval_state = {
  istate: Istate.t,
  estate: (exp, context),
};

let rec apply_actions = (is, ia) =>
  switch (ia) {
  | [] => is
  | [ia, ...iax] => apply_actions(apply_action(is, ia), iax)
  };
let incr_edit = (es: eval_state, act: action): (int, eval_state) => {
  let ia = to_iaction(act);
  let (t, is) = timed(() => apply_actions(es.istate, ia));
  let (_, es) = timed(() => step_trace(es.estate, act));
  (t, {istate: is, estate: es});
};

let incr_tyck = (es: eval_state, act: action): (int, eval_state) => {
  timed(() => {
    all_update_steps(es.istate);
    es;
  });
};

let baseline_edit = (es: eval_state, act: action): (int, eval_state) => {
  let ia = to_iaction(act);
  let (_, is) = timed(() => apply_actions(es.istate, ia));
  let (t, es) = timed(() => step_trace(es.estate, act));
  (t, {istate: is, estate: es});
};

let baseline_tyck = (es: eval_state, act: action): (int, eval_state) => {
  let bare_e = erase_upper(es.istate.ephemeral.root.root_child);
  let (t, _) =
    switch (act) {
    | Up
    | Down(_) => timed(() => ())
    | _ => timed(() => {performance_mark(bare_e)})
    };
  all_update_steps(es.istate);
  (t, es);
};

let should_skip = act =>
  switch (act) {
  | SDown(_)
  | SUp => true
  | Down(_)
  | Up => true
  | _ => false
  };
let init_eval_state = () => {istate: initial_state(), estate: (Hole, [])};
let handle =
    (
      name,
      edit: (eval_state, action) => (int, eval_state),
      tyck: (eval_state, action) => (int, eval_state),
    ) => {
  let acc = ref(init_eval_state());
  let timed =
    List.map(
      trace,
      act => {
        let (t, new_acc) = edit(acc^, act);
        let (t', new_acc') = tyck(new_acc, act);
        acc := new_acc';
        (act, (t, t'));
      },
    );
  let () =
    List.iteri(
      timed,
      (i, (act, (t, t'))) => {
        open Yojson.Basic;
        let json =
          `Assoc([
            ("name", `String(name)),
            ("action", `String("todo: fix")),
            ("iter", `Int(i)),
            ("edit_time", `Int(t)),
            ("tyck_time", `Int(t')),
            ("should_skip", `Bool(should_skip(act))),
          ]);
        Yojson.to_channel(c, json);
        Stdio.Out_channel.newline(c);
      },
    );
  ();
};

let () = handle("baseline", baseline_edit, baseline_tyck);
let () = handle("incr", incr_edit, incr_tyck);

let () = Stdio.Out_channel.close(c);