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

let set_max_right =
  fun
  | (Leaf, info, Leaf) => info.max_right = info.right
  | (Leaf, info, Node(_, infoR, _)) =>
    info.max_right = max(info.right, infoR.max_right)
  | (Node(_, infoL, _), info, Leaf) =>
    info.max_right = max(info.right, infoL.max_right)
  | (Node(_, infoL, _), info, Node(_, infoR, _)) =>
    info.max_right = max(info.right, max(infoL.max_right, infoR.max_right));

let build_node = (a, x, b) => {
  set_max_right((a, x, b));
  Node(a, x, b);
};

// postcondition: returns (l, v, r), and if [left] was present in the original triple, then [v.left == left]
let rec splay = (left: Order.t) =>
  fun
  // already root
  | (l, v, r) when left == v.left => (l, v, r)
  // not found
  | (Leaf, v, r) when left < v.left => (Leaf, v, r)
  // zig
  | (Node(ll, lv, lr), v, r) when left < v.left && left == lv.left => {
      let lr_v_r = build_node(lr, v, r);
      (ll, lv, lr_v_r);
    }
  // not found
  | (Node(Leaf, lv, lr), v, r) when left < v.left && left < lv.left => {
      let lr_v_r = build_node(lr, v, r);
      (Leaf, lv, lr_v_r);
    }
  // zig-zig
  | (Node(Node(lll, llv, llr), lv, lr), v, r)
      when left < v.left && left < lv.left => {
      let (lll, llv, llr) = splay(left, (lll, llv, llr));
      let lr_v_r = build_node(lr, v, r);
      let llr_lv_lr_v_r = build_node(llr, lv, lr_v_r);
      (lll, llv, llr_lv_lr_v_r);
    }
  // not found
  | (Node(ll, lv, Leaf), v, r) when left < v.left && left > lv.left => {
      let leaf_v_r = build_node(Leaf, v, r);
      (ll, lv, leaf_v_r);
    }
  // zig-zag
  | (Node(ll, lv, Node(lrl, lrv, lrr)), v, r)
      when left < v.left && left > lv.left => {
      let (lrl, lrv, lrr) = splay(left, (lrl, lrv, lrr));
      let ll_lr_lrl = build_node(ll, lv, lrl);
      let lrr_v_r = build_node(lrr, v, r);
      (ll_lr_lrl, lrv, lrr_v_r);
    }
  // not found
  | (l, v, Leaf) when left > v.left => (l, v, Leaf)
  // zag
  | (l, v, Node(rl, rv, rr)) when left > v.left && left == rv.left => {
      let l_v_rl = build_node(l, v, rl);
      (l_v_rl, rv, rr);
    }
  // not found
  | (l, v, Node(rl, rv, Leaf)) when left > v.left && left > rv.left => {
      let l_v_rl = build_node(l, v, rl);
      (l_v_rl, rv, Leaf);
    }
  // zag-zag
  | (l, v, Node(rl, rv, Node(rrl, rrv, rrr)))
      when left > v.left && left > rv.left => {
      let (rrl, rrv, rrr) = splay(left, (rrl, rrv, rrr));
      let l_v_rl = build_node(l, v, rl);
      let l_v_rl_rv_rrl = build_node(l_v_rl, rv, rrl);
      (l_v_rl_rv_rrl, rrv, rrr);
    }
  // not found
  | (l, v, Node(Leaf, rv, rr)) when left > v.left && left < rv.left => {
      let l_v_leaf = build_node(l, v, Leaf);
      (l_v_leaf, rv, rr);
    }
  // zag-zig
  | (l, v, Node(Node(rll, rlv, rlr), rv, rr))
      when left > v.left && left < rv.left => {
      let (rll, rlv, rlr) = splay(left, (rll, rlv, rlr));
      let l_v_rll = build_node(l, v, rll);
      let rlr_rv_rr = build_node(rlr, rv, rr);
      (l_v_rll, rlv, rlr_rv_rr);
    }
  | _ => failwith("impossible fallthrough: splay tree");

// returns (l, v), with the interpretation of (l, v, Leaf)
let rec splay_largest =
  fun
  | (l, v, Leaf) => (l, v)
  | (l, v, Node(rl, rv, Leaf)) => {
      let l_v_rl = build_node(l, v, rl);
      (l_v_rl, rv);
    }
  // zag-zag
  | (l, v, Node(rl, rv, Node(rrl, rrv, rrr))) => {
      let (rrl, rrv) = splay_largest((rrl, rrv, rrr));
      let l_v_rl = build_node(l, v, rl);
      let l_v_rl_rv_rrl = build_node(l_v_rl, rv, rrl);
      (l_v_rl_rv_rrl, rrv);
    };

let join: ((tree('a), tree('a))) => tree('a) =
  fun
  | (Leaf, t)
  | (t, Leaf) => t
  | (Node(ll, lv, lr), r) => {
      let (l, v) = splay_largest((ll, lv, lr));
      build_node(l, v, r);
    };

let rec insert_tree = (entry: 'a, left: Order.t, right: Order.t) =>
  fun
  | Leaf => {
      let info = {entry, left, right, max_right: right};
      (Leaf, info, Leaf);
    }
  // already present
  | Node(l, v, r) when left == v.left => (l, v, r)
  | Node(l, v, r) when left < v.left => {
      let (ll, lv, lr) = insert_tree(entry, left, right, l);
      let ll_lv_lr = build_node(ll, lv, lr);
      (ll_lv_lr, v, r);
    }
  | Node(l, v, r) when left > v.left => {
      let (rl, rv, rr) = insert_tree(entry, left, right, r);
      let rl_rv_rr = build_node(rl, rv, rr);
      (l, v, rl_rv_rr);
    }
  | _ => failwith("impossible fallthrough: splay tree");

let insert = (entry: 'a, left: Order.t, right: Order.t, t: tree('a)) => {
  let (l, v, r) = insert_tree(entry, left, right, t);
  splay(left, (l, v, r));
};

let delete = (left: Order.t) =>
  fun
  | Leaf => Leaf
  | Node(l, v, r) => {
      let (l, v, r) = splay(left, (l, v, r));
      // only delete if [left] appears in the tree (and therefore is now at the root)
      if (v.left == left) {
        join((l, r));
      } else {
        build_node(l, v, r);
      };
    };

let rec find_tightest_container = (left: Order.t) =>
  fun
  | Leaf => None
  | Node(_, v, _) when left == v.left =>
    failwith("input should be var, tree should hold binders")
  | Node(l, v, _) when left < v.left => find_tightest_container(left, l)
  | Node(_, v, _) when left > v.max_right => None
  | Node(l, v, r) => {
      // v.left <= left <= v.max_right
      switch (find_tightest_container(left, r)) {
      | Some(v) => Some(v)
      | None when left < v.right => v.entry
      | None => find_tightest_container(left, l)
      };
    };
