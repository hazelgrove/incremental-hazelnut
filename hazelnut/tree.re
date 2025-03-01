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
}

and tree('a) =
  | Leaf
  | Node(color, tree('a), info('a), tree('a));

let set_max_right =
  fun
  | (Leaf, info, Leaf) => info.max_right = info.right
  | (Leaf, info, Node(_, _, infoR, _)) =>
    info.max_right = max(info.right, infoR.max_right)
  | (Node(_, _, infoL, _), info, Leaf) =>
    info.max_right = max(info.right, infoL.max_right)
  | (Node(_, _, infoL, _), info, Node(_, _, infoR, _)) =>
    info.max_right = max(info.right, max(infoL.max_right, infoR.max_right));

let build_node = (color, a, x, b) => {
  set_max_right((a, x, b));
  Node(color, a, x, b);
};

let balance: ((color, tree('a), info('a), tree('a))) => tree('a) =
  fun
  | (B, Node(R, Node(R, a, x, b), y, c), z, d)
  | (B, Node(R, a, x, Node(R, b, y, c)), z, d)
  | (B, a, x, Node(R, Node(R, b, y, c), z, d))
  | (B, a, x, Node(R, b, y, Node(R, c, z, d))) => {
      let axb = build_node(B, a, x, b);
      let czd = build_node(B, c, z, d);
      build_node(R, axb, y, czd);
    }
  | (BB, Node(R, a, x, Node(R, b, y, c)), z, d)
  | (BB, a, x, Node(R, b, y, Node(R, c, z, d))) => {
      let axb = build_node(B, a, x, b);
      let czd = build_node(B, c, z, d);
      build_node(B, axb, y, czd);
    }
  | (color, a, x, b) => build_node(color, a, x, b);

let rotate: ((color, tree('a), info('a), tree('a))) => tree('a) =
  fun
  | (R, Node(BB, a, x, b), y, Node(B, c, z, d)) => {
      let axb = build_node(B, a, x, b);
      let axbyc = build_node(R, axb, y, c);
      balance((B, axbyc, z, d));
    }
  | (R, Node(B, a, x, b), y, Node(BB, c, z, d)) => {
      let czd = build_node(B, c, z, d);
      let byczd = build_node(R, b, y, czd);
      balance((B, a, x, byczd));
    }
  | (B, Node(BB, a, x, b), y, Node(B, c, z, d)) => {
      let axb = build_node(B, a, x, b);
      let axbyc = build_node(R, axb, y, c);
      balance((BB, axbyc, z, d));
    }
  | (B, Node(B, a, x, b), y, Node(BB, c, z, d)) => {
      let czd = build_node(B, c, z, d);
      let byczd = build_node(R, b, y, czd);
      balance((BB, a, x, byczd));
    }
  | (B, Node(BB, a, w, b), x, Node(R, Node(B, c, y, d), z, e)) => {
      let awb = build_node(B, a, w, b);
      let awbxc = build_node(R, awb, x, c);
      let awbyc = balance((B, awbxc, y, d));
      build_node(B, awbyc, z, e);
    }
  | (B, Node(R, a, w, Node(B, b, x, c)), y, Node(BB, d, z, e)) => {
      let dze = build_node(B, d, z, e);
      let cydze = build_node(R, c, y, dze);
      let bxcydze = balance((B, b, x, cydze));
      build_node(B, a, w, bxcydze);
    }
  | (color, a, x, b) => build_node(color, a, x, b);

let blacken =
  fun
  | Node(R, a, x, b) => Node(B, a, x, b)
  | tree => tree;

let insert = (entry: 'a, left: Order.t, right: Order.t, tree: tree('a)) => {
  let rec ins =
    fun
    | Leaf => Node(R, Leaf, {entry, left, right, max_right: right}, Leaf)
    | Node(color, childL, info, childR) =>
      if (Order.compare(left, info.left) < 0) {
        balance((color, ins(childL), info, childR));
      } else if (Order.compare(left, info.left) > 0) {
        balance((color, childL, info, ins(childR)));
      } else {
        Node(color, childL, info, childR);
      };
  blacken(ins(tree));
};

let redden =
  fun
  | Node(B, Node(B, a, x, b), y, Node(B, c, z, d)) =>
    Node(R, Node(B, a, x, b), y, Node(B, c, z, d))
  | tree => tree;

let delete = (entry: 'a, tree: tree('a)) => {
  let rec del =
    fun
    | Leaf => Leaf
    | Node(R, Leaf, info, Leaf) when info.entry === entry => Leaf
    | Node(B, Leaf, info, Leaf) when info.entry === entry => Node()
    | Node(B, Node(R, a, x, b), info, Leaf) when info.entry === entry =>
      Node(B, a, x, b);

  // | Node(Red, Node(Black, a, x, b), y, Node(Black, c, z, d)) =>
  del(redden(tree));
};
