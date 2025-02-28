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
  | List(exp)
  | Int
  | Nil(exp)
  | Cons(exp, exp)
  | /** list, nil body, head, tail, cons body */
    ListMatch(
      exp,
      exp,
      exp,
      exp,
      exp,
    )
  | ITE(exp, exp, exp)
  | App(exp, exp);

let merge =
  Lam(
    Var("xsys"),
    Prod(List(Int), List(Int)),
    ListMatch(
      Zro(Var("xsys")),
      Fst(Var("xsys")),
      Var("x"),
      Var("xs"),
      ListMatch(
        Fst(Var("xsys")),
        Cons(Var("x"), Var("xs")),
        Var("y"),
        Var("ys"),
        ITE(
          App(Var("lt"), Tup(Var("x"), Var("y"))),
          Cons(
            Var("x"),
            App(
              Var("merge"),
              Tup(Var("xs"), Cons(Var("y"), Var("ys"))),
            ),
          ),
          Cons(
            Var("y"),
            App(
              Var("merge"),
              Tup(Cons(Var("x"), Var("xs")), Var("ys")),
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
    List(Int),
    ListMatch(
      Var("xs"),
      Tup(Nil(Int), Nil(Int)),
      Var("x"),
      Var("xs"),
      Let(
        Var("yszs"),
        App(Var("split"), Var("xs")),
        Tup(Cons(Var("x"), Fst(Var("yszs"))), Zro(Var("yszs"))),
      ),
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
    List(Int),
    ListMatch(
      Var("xs"),
      Nil(Int),
      Var("x"),
      Var("xs"),
      ListMatch(
        Var("xs"),
        Nil(Int),
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
  | Lit(i) => string(string_of_int(i))
  | Lam(arg_name, arg_type, body) =>
    string("fun ")
    ^^ pprint(arg_name)
    ^^ string(": ")
    ^^ pprint(arg_type)
    ^^ string(" -> ")
    ^^ pprint(body)
  | List(t) => string("[") ^^ pprint(t) ^^ string("]")
  | Prod(x, y) => pprint(x) ^^ string(" * ") ^^ pprint(y)
  | Int => string("int")
  | Zro(x) => pprint(x) ^^ string(".0")
  | Fst(x) => pprint(x) ^^ string(".1")
  | Nil(ty) => string("[]@") ^^ pprint(ty)
  | Cons(x, xs) => pprint(x) ^^ string(" :: ") ^^ pprint(xs)
  | ITE(i, t, e) =>
    string("if ")
    ^^ pprint(i)
    ^^ break(1)
    ^^ string("then ")
    ^^ pprint(t)
    ^^ break(1)
    ^^ string("else ")
    ^^ pprint(e)
  };

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
  | List(t) => "List"
  | Prod(x, y) => "Prod"
  | Int => "Int"
  | Zro(x) => "Zro"
  | Fst(x) => "Fst"
  | Nil(ty) => "Nil"
  | Cons(x, xs) => "Cons"
  | ITE(i, t, e) => "Ite"
  };

let pretty_print = x => {
  PPrint.ToChannel.pretty(0.8, 160, Stdio.Out_channel.stdout, pprint(x));
  print_endline("");
};

type action =
  | Down(int)
  | Up
  | Replace(exp);

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
  | ITE(i, t, e) =>
    [Replace(ITE(Hole, Hole, Hole))]
    @ List.join(shuffle([subedits(i, 0), subedits(t, 1), subedits(e, 2)]))
  | App(f, xs) =>
    [Replace(App(Hole, Hole))]
    @ List.join(shuffle([subedits(f, 0), subedits(xs, 1)]))
  | Tup(l, r) =>
    [Replace(Tup(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Prod(l, r) =>
    [Replace(Prod(Hole, Hole))]
    @ List.join(shuffle([subedits(l, 0), subedits(r, 1)]))
  | Cons(x, xs) =>
    [Replace(Cons(Hole, Hole))]
    @ List.join(shuffle([subedits(x, 0), subedits(xs, 1)]))
  | Zro(x) => [Replace(Zro(Hole))] @ subedits(x, 0)
  | Fst(x) => [Replace(Fst(Hole))] @ subedits(x, 0)
  | Nil(x) => [Replace(Nil(Hole))] @ subedits(x, 0)
  | List(x) => [Replace(List(Hole))] @ subedits(x, 0)
  | Var(_)
  | Int => [Replace(x)]
  | _ =>
    pretty_print(x);
    failwith("edits");
  };
};

let trace = edits(program);

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
  | ITE(ii, t, e) =>
    if (i == 0) {
      (ii, [(x => ITE(x, t, e)), ...ctx]);
    } else if (i == 1) {
      (t, [(x => Let(ii, x, e)), ...ctx]);
    } else if (i == 2) {
      (e, [(x => Let(ii, t, x)), ...ctx]);
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
  | List(x) =>
    if (i == 0) {
      (x, [(x => List(x)), ...ctx]);
    } else {
      failwith("bad");
    }
  | Nil(x) =>
    if (i == 0) {
      (x, [(x => Nil(x)), ...ctx]);
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
  | Cons(x, y) =>
    if (i == 0) {
      (x, [(x => Cons(x, y)), ...ctx]);
    } else if (i == 1) {
      (y, [(y => Cons(x, y)), ...ctx]);
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
    print_endline(case_name(x));
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

apply_traces(Hole, [], trace);
