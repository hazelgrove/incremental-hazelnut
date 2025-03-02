open Order;

// implementation based on: doi:10.1017/S0956796814000227

type color =
  | BB // double black, see the 2014 paper
  | B
  | R;

type info('a) = {
  entry: 'a,
  left: Order.t,
  right: Order.t,
  mutable max_right: Order.t,
};

type node('a) =
  | Leaf
  | N(tree('a), info('a), tree('a))

and tree('a) =
  | C(color, node('a));

let set_max_right =
  fun
  | (Leaf, info, Leaf) => info.max_right = info.right
  | (Leaf, info, N(_, infoR, _)) =>
    info.max_right = max(info.right, infoR.max_right)
  | (N(_, infoL, _), info, Leaf) =>
    info.max_right = max(info.right, infoL.max_right)
  | (N(_, infoL, _), info, N(_, infoR, _)) =>
    info.max_right = max(info.right, max(infoL.max_right, infoR.max_right));

let set_max_right_color =
  fun
  | (C(_, a), x, C(_, b)) => set_max_right((a, x, b));

let build_node = (color, a, x, b) => {
  set_max_right_color((a, x, b));
  C(color, N(a, x, b));
};

let balance: ((color, tree('a), info('a), tree('a))) => tree('a) =
  fun
  | (B, C(R, N(C(R, N(a, x, b)), y, c)), z, d)
  | (B, C(R, N(a, x, C(R, N(b, y, c)))), z, d)
  | (B, a, x, C(R, N(C(R, N(b, y, c)), z, d)))
  | (B, a, x, C(R, N(b, y, C(R, N(c, z, d))))) => {
      let axb = build_node(B, a, x, b);
      let czd = build_node(B, c, z, d);
      build_node(R, axb, y, czd);
    }
  | (BB, C(R, N(a, x, C(R, N(b, y, c)))), z, d)
  | (BB, a, x, C(R, N(b, y, C(R, N(c, z, d))))) => {
      let axb = build_node(B, a, x, b);
      let czd = build_node(B, c, z, d);
      build_node(B, axb, y, czd);
    }
  | (color, a, x, b) => build_node(color, a, x, b);

let rotate: ((color, tree('a), info('a), tree('a))) => tree('a) =
  fun
  | (R, C(BB, axb), y, C(B, N(c, z, d))) => {
      let axbyc = build_node(R, C(B, axb), y, c);
      balance((B, axbyc, z, d));
    }
  | (R, C(B, N(a, x, b)), y, C(BB, czd)) => {
      let byczd = build_node(R, b, y, C(B, czd));
      balance((B, a, x, byczd));
    }
  | (B, C(BB, axb), y, C(B, N(c, z, d))) => {
      let axbyc = build_node(R, C(B, axb), y, c);
      balance((BB, axbyc, z, d));
    }
  | (B, C(B, N(a, x, b)), y, C(BB, czd)) => {
      let byczd = build_node(R, b, y, C(B, czd));
      balance((BB, a, x, byczd));
    }
  | (B, C(BB, awb), x, C(R, N(C(B, N(c, y, d)), z, e))) => {
      let awbxc = build_node(R, C(B, awb), x, c);
      let awbyc = balance((B, awbxc, y, d));
      build_node(B, awbyc, z, e);
    }
  | (B, C(R, N(a, w, C(B, N(b, x, c)))), y, C(BB, dze)) => {
      let cydze = build_node(R, c, y, C(B, dze));
      let bxcydze = balance((B, b, x, cydze));
      build_node(B, a, w, bxcydze);
    }
  | (color, a, x, b) => build_node(color, a, x, b);

let blacken =
  fun
  | C(R, a) => C(B, a)
  | tree => tree;

let insert = (entry: 'a, left: Order.t, right: Order.t, tree: tree('a)) => {
  let rec ins =
    fun
    | C(_, Leaf) => {
        let info = {entry, left, right, max_right: right};
        C(R, N(C(B, Leaf), info, C(B, Leaf)));
      }
    | C(color, N(childL, info, childR)) =>
      if (Order.compare(left, info.left) < 0) {
        balance((color, ins(childL), info, childR));
      } else if (Order.compare(left, info.left) > 0) {
        balance((color, childL, info, ins(childR)));
      } else {
        C(color, N(childL, info, childR));
      };
  blacken(ins(tree));
};

let redden =
  fun
  | C(B, N(C(B, a), x, C(B, b))) => C(R, N(C(B, a), x, C(B, b)))
  | tree => tree;

let delete = (entry: 'a, left: Order.t, _right: Order.t, tree: tree('a)) => {
  let rec del =
    fun
    | C(BB, Leaf) => failwith("impossible (tree.re)")
    | C(R, Leaf) => failwith("impossible (tree.re)")
    | C(B, Leaf) => C(B, Leaf)
    | C(R, N(C(B, Leaf), info, C(B, Leaf))) when info.entry === entry =>
      C(B, Leaf)
    | C(R, N(C(R, N(a, x, b)), info, C(B, Leaf)))
        when info.entry === entry =>
      C(B, N(a, x, b))
    | C(B, N(C(B, Leaf), info, C(B, Leaf))) when info.entry === entry =>
      C(BB, Leaf)
    | C(color, N(childL, info, childR)) =>
      if (Order.compare(left, info.left) < 0) {
        rotate((color, del(childL), info, childR));
      } else if (Order.compare(left, info.left) > 0) {
        rotate((color, childL, info, del(childR)));
      } else {
        failwith("todo");
      };
  del(redden(tree));
};
