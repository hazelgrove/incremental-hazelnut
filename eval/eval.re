open Sys;
open Yojson;
open Unix;
open Core;
open PPrint;
open Hazelnut_lib.Pexp;
open Hazelnut_lib.Incremental;
open Hazelnut_lib.State;
open Hazelnut_lib.Actions;
open Hazelnut_lib.Actions_random;
open Hazelnut_lib.Update;
open Hazelnut_lib.Marking;
open Ocaml_intrinsics;

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

let incr_tyck = (es: Istate.t): (int, Istate.t) => {
  timed(() => {
    all_update_steps(es);
    es;
  });
};

let baseline_tyck = (es: Istate.t): (int, Istate.t) => {
  let bare_e = erase_upper(es.ephemeral.root.root_child);
  let (t, _) = timed(() => {performance_mark(bare_e)});
  all_update_steps(es);
  (t, es);
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
  | /** list, nil body, head, tail, cons body */
    ListMatch(
      exp,
      exp,
      exp,
      exp,
      exp,
    )
  | /** 'a -> (Num -> 'a -> 'a) -> List -> 'a */
    ListRec(exp)
  | ITE(exp)
  | App(exp, exp);

// should only be one level deep - an node where all children is Hole
type hexp = exp;

type action =
  | Down(int)
  | Up
  | Replace(hexp)
  | ReplaceDown(int)
  | ReplaceUp(hexp, int);

let app2 = (f: exp, a: exp, b: exp) => App(App(f, a), b);

let app3 = (f: exp, a: exp, b: exp, c: exp) => App(app2(f, a, b), c);

let const = (x: exp) => Lam(Var("_"), Unit, x);

let lam2 = (x: exp, xt: exp, y: exp, yt: exp, b: exp) =>
  Lam(x, xt, Lam(y, yt, b));

let ite = (i, ty, t, e) => app3(ITE(i), ty, const(t), const(e));

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
let cons = (x: exp, xs: exp) => app2(Cons, x, xs);
let merge =
  lam2(
    Var("xs"),
    List,
    Var("ys"),
    List,
    list_rec(
      List,
      Var("ys"),
      Var("x"),
      Var("xs"),
      list_rec(
        List,
        cons(Var("x"), Var("xs")),
        Var("y"),
        Var("ys"),
        Var("ys"),
        Var("ys"),
      ),
      Var("xs"),
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
let mergesort =
  Lam(
    Var("xs"),
    List,
    ListMatch(
      Var("xs"),
      Nil,
      Var("x"),
      Var("xs"),
      ListMatch(
        Var("xs"),
        Nil,
        Var("_"),
        Var("_"),
        Let(
          Var("yszs"),
          App(Var("split"), Var("xs")),
          Let(
            Var("ys"),
            App(Var("mergesort"), Zro(Var("yszs"))),
            Let(
              Var("zs"),
              App(Var("mergesort"), Fst(Var("yszs"))),
              App(Var("merge"), Tup(Var("ys"), Var("zs"))),
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
let map_lists = Hole;
/** map_lists : (((Int, Int) -> Int), [Int,Int]) -> [Int] =
  fun (f, l) ->
    case l
      | [] => []
      | x::xs => f(x) :: map_lists(f, xs)
    end */

let lefts = Hole;
/**lefts = map_lists(fun (x, _) -> x, _) */
let rights = Hole;
/**rights = map_lists(fun (_,x) -> x, _)  */
let zip = Hole;
/**zip : ([Int],[Int]) -> [(Int, Int)] =
  fun (xs, ys) ->
    case xs
      | [] => []
      | x::xs =>
      case ys
        | [] => []
        | y::ys => (x,y)::zip(xs, ys)
      end
    end */
let sum = Hole;
/**sum : [Int] -> Int =
  fun xs ->
    case xs
      | [] => 0
      | x::xs => x + sum(xs)
     */
let input_width = Hole;
/** input_width = 1 */
let parse = Hole;
/**parse : String -> [(Int, Int)] =
  fun s ->
    if string_length(s) >= input_width * 2 + 3 then
      (int_of_string(string_sub(s,0,input_width)), int_of_string(string_sub(s,input_width+3,input_width)))
      ::
      (parse(string_sub(s, input_width * 2 + 5, string_length(s) - (input_width * 2 + 5))))
    else
      [] */
let input = Hole;
/**3   4\n4   3\n2   5\n1   3\n3   9\n3   3  */
let parsed = Hole;
/**parse(input ++ \n) */
let l = Hole;
/** parsed |> lefts |> mergesort*/
let r = Hole;
/** parsed |> rights |> mergesort*/

let program =
  Let(
    Var("merge"),
    merge,
    Let(
      Var("split"),
      split,
      Let(
        Var("mergesort"),
        mergesort,
        Let(
          Var("lefts"),
          lefts,
          Let(
            Var("rights"),
            rights,
            Let(
              Var("zip"),
              zip,
              Let(
                Var("sum"),
                sum,
                Let(
                  Var("input_width"),
                  input_width,
                  Let(
                    Var("parse"),
                    parse,
                    Let(
                      Var("input"),
                      input,
                      Let(
                        Var("parsed"),
                        parsed,
                        Let(Var("l"), l, Let(Var("r"), r, Hole)),
                      ),
                    ),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    ),
  );
/**(l,r)
|> zip
|> map_lists(fun x,y -> abs(x-y), _)
|> sum */

let program =
  Let(
    Var("merge"),
    merge,
    Let(
      Var("split"),
      split,
      Let(Var("mergesort"), mergesort, Var("mergesort")),
    ),
  );

let program =
  Let(
    Var("merge"),
    merge,
    Let(Var("split"), split, Tup(Var("merge"), Var("split"))),
  );

let program = merge;

let rec case_name = (x: exp): string =>
  switch (x) {
  | Hole => "Hole"
  | Var(v) => "Var"
  | App(f, xs) => "App"
  | Let(lhs, rhs, body) => "Let"
  | ListMatch(l, nil_case, head, tail, cons_case) => "ListMatch"
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
  | ListMatch(l, nil_case, head, tail, cons_case) =>
    string("case ")
    ^^ pprint(l)
    ^^ group(
         break(1)
         ^^ string("| [] => ")
         ^^ pprint(nil_case)
         ^^ break(1)
         ^^ string("| ")
         ^^ pprint(head)
         ^^ string(" :: ")
         ^^ pprint(tail)
         ^^ string(" => ")
         ^^ pprint(cons_case),
       )
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
  | _ =>
    print_endline(case_name(x));
    failwith("pprint");
  };

let rec pprint_action = (x: action): PPrint.document =>
  switch (x) {
  | Up => string("Up")
  | Down(i) => string("Down " ++ string_of_int(i))
  | Replace(x) => string("Replace ") ^^ pprint(x)
  | ReplaceDown(i) => string("ReplaceDown " ++ string_of_int(i))
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

type context = list(exp => exp);

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
  | ListMatch(l, nil_case, head, tail, cons_case) =>
    [Replace(ListMatch(Hole, Hole, Hole, Hole, Hole))]
    @ List.join(
        shuffle([
          subedits(l, 0),
          subedits(nil_case, 1),
          subedits(head, 2),
          subedits(tail, 3),
          subedits(cons_case, 4),
        ]),
      )
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

let wrap_insert = [
  ReplaceUp(Lam(Hole, Hole, Hole), 2),
  Down(0),
  Replace(Var("x")),
  Up,
  Down(1),
  Replace(Int),
  Up,
];
let wrap_delete = [ReplaceDown(2)];
let trace =
  wrap_insert @ wrap_insert @ edits(program) @ wrap_delete @ wrap_delete;

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
  | ListMatch(l, nil_case, head, tail, cons_case) =>
    if (i == 0) {
      (l, [(x => ListMatch(x, nil_case, head, tail, cons_case)), ...ctx]);
    } else if (i == 1) {
      (nil_case, [(x => ListMatch(l, x, head, tail, cons_case)), ...ctx]);
    } else if (i == 2) {
      (head, [(x => ListMatch(l, nil_case, x, tail, cons_case)), ...ctx]);
    } else if (i == 3) {
      (tail, [(x => ListMatch(l, nil_case, head, x, cons_case)), ...ctx]);
    } else if (i == 4) {
      (cons_case, [(x => ListMatch(l, nil_case, head, tail, x)), ...ctx]);
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
  | _ =>
    pretty_print(x);
    failwith("godown");
  };

let go_up = (x: exp, ctx: context): (exp, context) =>
  switch (ctx) {
  | [c, ...ctx] => (c(x), ctx)
  };

let rec uppest = (x: exp, ctx: context) =>
  switch (ctx) {
  | [] => x
  | [c, ...ctx] => uppest(c(x), ctx)
  };
let step_trace = (x: exp, ctx: context, act: action): (exp, context) => {
  switch (act) {
  | Down(i) => go_down(x, ctx, i)
  | Up => go_up(x, ctx)
  | Replace(x) => (x, ctx)
  };
};

let rec apply_traces = (x: exp, ctx: context, act) => {
  if (false && List.length(ctx) % 10 == 0) {
    pretty_print(uppest(x, ctx));
  };
  switch (act) {
  | [] => x
  | [act, ...acts] =>
    let (x, ctx) = step_trace(x, ctx, act);
    apply_traces(x, ctx, acts);
  };
};

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
  | Up => Iaction.MoveUp
  | ReplaceUp(Lam(Hole, Hole, Hole), 2) => Iaction.WrapLam
  | Replace(Lam(Hole, Hole, Hole)) => Iaction.WrapLam
  | Replace(App(Hole, Hole)) => Iaction.WrapAp(One)
  | Replace(ListRec(Hole)) => Iaction.InsertListRec
  | Replace(Cons) => Iaction.InsertCons
  | Replace(Var(x)) => Iaction.InsertVar(x)
  | Replace(Int) => Iaction.InsertNumType
  | Replace(List) => Iaction.InsertList
  | Down(0) => Iaction.MoveDown(One)
  | Down(1) => Iaction.MoveDown(Two)
  | Down(2) => Iaction.MoveDown(Three)
  | ReplaceDown(2) => Iaction.Unwrap(Three)
  | _ =>
    pretty_print_action(act);
    failwith("to_iaction");
  };
};
let actions: list(Iaction.t) = List.map(trace, to_iaction);

let handle = (name, f) => {
  let acc = ref(initial_state());
  let timed =
    List.map(
      actions,
      act => {
        let (t, e) = f(apply_action(acc^, act));
        acc := e;
        (act, t);
      },
    );
  let () =
    List.iteri(
      timed,
      (i, (act, t)) => {
        open Yojson.Basic;
        let json =
          `Assoc([
            ("name", `String(name)),
            ("action", `String(string_of_action(act))),
            ("iter", `Int(i)),
            ("time", `Int(t)),
          ]);
        Yojson.to_channel(c, json);
        Stdio.Out_channel.newline(c);
      },
    );
  ();
};

let () = handle("baseline", baseline_tyck);
let () = handle("incr", incr_tyck);

let () = Stdio.Out_channel.close(c);
