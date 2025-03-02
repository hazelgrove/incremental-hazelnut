open Order;

// https://www.cs.cornell.edu/courses/cs3110/2013sp/recitations/rec08-splay/rec08.html

type info('a) = {
  entry: 'a,
  left: Order.t,
  right: Order.t,
  mutable max_right: Order.t,
};

type tree('a) =
  | Leaf
  | Node(tree('a), info('a), tree('a));

let rec splay = (left: Order.t) =>
  fun
  // already root
  | (l, v, r) when left == v.left => (l, v, r)
  // not found
  | (Leaf, v, r) when left < v.left => (Leaf, v, r)
  // zig
  | (Node(ll, lv, lr), v, r) when left < v.left && left == lv.left => {
      (ll, lv, Node(lr, v, r));
    }
  // not found
  | (Node(Leaf, lv, lr), v, r) when left < v.left && left < lv.left => {
      (Leaf, lv, Node(lr, v, r));
    }
  // zig-zig
  | (Node(Node(lll, llv, llr), lv, lr), v, r)
      when left < v.left && left < lv.left => {
      let (lll', llv', llr') = splay(left, (lll, llv, llr));
      (lll', llv', Node(llr', lv, Node(lr, v, r)));
    }
  // not found
  | (Node(ll, lv, Leaf), v, r) when left < v.left && left > lv.left => {
      (ll, lv, Node(Leaf, v, r));
    }
  // zig-zag
  | (Node(ll, lv, Node(lrl, lrv, lrr)), v, r)
      when left < v.left && left > lv.left => {
      let (lrl', lrv', lrr') = splay(left, (lrl, lrv, lrr));
      (Node(ll, lv, lrl'), lrv', Node(lrr', v, r));
    }
  // not found
  | (l, v, Leaf) when left > v.left => (l, v, Leaf)
  // zag
  | (l, v, Node(rl, rv, rr)) when left > v.left && left == rv.left => {
      (Node(l, v, rl), rv, rr);
    }
  // not found
  | (l, v, Node(rl, rv, Leaf)) when left > v.left && left > rv.left => {
      (Node(l, v, rl), rv, Leaf);
    }
  // zag-zag
  | (l, v, Node(rl, rv, Node(rrl, rrv, rrr)))
      when left > v.left && left > rv.left => {
      let (rrl', rrv', rrr') = splay(left, (rrl, rrv, rrr));
      (Node(Node(l, v, rl), rv, rrl'), rrv', rrr');
    }
  // not found
  | (l, v, Node(Leaf, rv, rr)) when left > v.left && left < rv.left => {
      (Node(l, v, Leaf), rv, rr);
    }
  // zag-zig
  | (l, v, Node(Node(rll, rlv, rlr), rv, rr))
      when left > v.left && left < rv.left => {
      let (rll', rlv', rlr') = splay(left, (rll, rlv, rlr));
      (Node(l, v, rll'), rlv', Node(rlr', rv, rr));
    }
  | _ => failwith("impossible fallthrough: splay tree");
