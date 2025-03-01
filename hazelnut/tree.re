open Order;

type color =
  | Black
  | Red;

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

let balance: ((color, tree('a), info('a), tree('a))) => tree('a) =
  fun
  | (Black, Node(Red, Node(Red, a, x, b), y, c), z, d)
  | (Black, Node(Red, a, x, Node(Red, b, y, c)), z, d)
  | (Black, a, x, Node(Red, Node(Red, b, y, c), z, d))
  | (Black, a, x, Node(Red, b, y, Node(Red, c, z, d))) => {
      set_max_right((a, x, b));
      set_max_right((c, z, d));
      set_max_right((Node(Black, a, x, b), y, Node(Black, c, z, d)));
      Node(Red, Node(Black, a, x, b), y, Node(Black, c, z, d));
    }
  | (a, b, c, d) => Node(a, b, c, d);

let insert = (entry: 'a, left: Order.t, right: Order.t, tree: tree('a)) => {
  let rec insert_rec =
    fun
    | Leaf => Node(Red, Leaf, {entry, left, right, max_right: right}, Leaf)
    | Node(color, childL, info, childR) =>
      if (Order.compare(left, info.left) < 0) {
        balance((color, insert_rec(childL), info, childR));
      } else if (Order.compare(left, info.left) > 0) {
        balance((color, childL, info, insert_rec(childR)));
      } else {
        Node(color, childL, info, childR);
      };
  switch (insert_rec(tree)) {
  | Leaf => failwith("impossible (tree.re)")
  | Node(_, childL, info, childR) => Node(Black, childL, info, childR)
  };
};
