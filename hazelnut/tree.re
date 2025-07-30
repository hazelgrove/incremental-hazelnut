open Order;

// https://www.cs.cornell.edu/courses/cs3110/2013sp/recitations/rec08-splay/rec08.html

module Tree = {
  [@deriving sexp]
  type info('a) = {
    entry: 'a,
    left: Order.t,
    right: Order.t,
    mutable max_right: Order.t,
  };

  [@deriving sexp]
  type t('a) =
    | Leaf
    | Node(t('a), info('a), t('a));

  let unnode: t('a) => (t('a), info('a), t('a)) =
    fun
    | Leaf => failwith("unnode")
    | Node(l, v, r) => (l, v, r);

  let rec assert_order_invariant: t('a) => unit =
    fun
    | Leaf => ()
    | Node(l, info, right) => {
        // Left comparison
        switch (l) {
        | Leaf => ()
        | Node(_, l_info, _) => assert(!Order.lt(info.left, l_info.left))
        };

        // Left subtree
        assert_order_invariant(l);

        // Right comparison
        switch (right) {
        | Leaf => ()
        | Node(_, right_info, _) =>
          assert(!Order.gt(info.left, right_info.left))
        };
        // Right subtree
        assert_order_invariant(right);
      };

  let empty = Leaf;

  let is_empty =
    fun
    | Leaf => true
    | _ => false;

  let rec iter = f =>
    fun
    | Leaf => ()
    | Node(l, v, r) => {
        f(v.entry);
        iter(f, l);
        iter(f, r);
      };

  let rec list_of_t: t('a) => list('a) =
    fun
    | Leaf => []
    | Node(l, v, r) => list_of_t(l) @ [v.entry] @ list_of_t(r);

  let set_max_right =
    fun
    | (Leaf, info, Leaf) => info.max_right = info.right
    | (Leaf, info, Node(_, infoR, _)) =>
      info.max_right = Order.max(info.right, infoR.max_right)
    | (Node(_, infoL, _), info, Leaf) =>
      info.max_right = Order.max(info.right, infoL.max_right)
    | (Node(_, infoL, _), info, Node(_, infoR, _)) =>
      info.max_right =
        Order.max(info.right, Order.max(infoL.max_right, infoR.max_right));

  // smart constructor for Node
  let node = (a, x, b) => {
    set_max_right((a, x, b));
    Node(a, x, b);
  };

  let lt = Order.lt;
  let eq = Order.eq;
  let gt = Order.gt;

  // postcondition: returns (l, v, r), and if [left] was present in the original triple, then [v.left == left]
  let rec splay = (left: Order.t) => {
    fun
    // already root
    | (l, v, r) when eq(left, v.left) => (l, v, r)
    // not found
    | (Leaf, v, r) when lt(left, v.left) => (Leaf, v, r)
    // zig
    | (Node(ll, lv, lr), v, r) when lt(left, v.left) && eq(left, lv.left) => {
        let lr_v_r = node(lr, v, r);
        (ll, lv, lr_v_r);
      }
    // not found
    | (Node(Leaf, lv, lr), v, r) when lt(left, v.left) && lt(left, lv.left) => {
        let lr_v_r = node(lr, v, r);
        (Leaf, lv, lr_v_r);
      }
    // zig-zig
    | (Node(Node(lll, llv, llr), lv, lr), v, r)
        when lt(left, v.left) && lt(left, lv.left) => {
        let (lll, llv, llr) = splay(left, (lll, llv, llr));
        let lr_v_r = node(lr, v, r);
        let llr_lv_lr_v_r = node(llr, lv, lr_v_r);
        (lll, llv, llr_lv_lr_v_r);
      }
    // not found
    | (Node(ll, lv, Leaf), v, r) when lt(left, v.left) && gt(left, lv.left) => {
        let leaf_v_r = node(Leaf, v, r);
        (ll, lv, leaf_v_r);
      }
    // zig-zag
    | (Node(ll, lv, Node(lrl, lrv, lrr)), v, r)
        when lt(left, v.left) && gt(left, lv.left) => {
        let (lrl, lrv, lrr) = splay(left, (lrl, lrv, lrr));
        let ll_lr_lrl = node(ll, lv, lrl);
        let lrr_v_r = node(lrr, v, r);
        (ll_lr_lrl, lrv, lrr_v_r);
      }
    // not found
    | (l, v, Leaf) when gt(left, v.left) => (l, v, Leaf)
    // zag
    | (l, v, Node(rl, rv, rr)) when gt(left, v.left) && eq(left, rv.left) => {
        let l_v_rl = node(l, v, rl);
        (l_v_rl, rv, rr);
      }
    // not found
    | (l, v, Node(rl, rv, Leaf)) when gt(left, v.left) && gt(left, rv.left) => {
        let l_v_rl = node(l, v, rl);
        (l_v_rl, rv, Leaf);
      }
    // zag-zag
    | (l, v, Node(rl, rv, Node(rrl, rrv, rrr)))
        when gt(left, v.left) && gt(left, rv.left) => {
        let (rrl, rrv, rrr) = splay(left, (rrl, rrv, rrr));
        let l_v_rl = node(l, v, rl);
        let l_v_rl_rv_rrl = node(l_v_rl, rv, rrl);
        (l_v_rl_rv_rrl, rrv, rrr);
      }
    // not found
    | (l, v, Node(Leaf, rv, rr)) when gt(left, v.left) && lt(left, rv.left) => {
        let l_v_leaf = node(l, v, Leaf);
        (l_v_leaf, rv, rr);
      }
    // zag-zig
    | (l, v, Node(Node(rll, rlv, rlr), rv, rr))
        when gt(left, v.left) && lt(left, rv.left) => {
        let (rll, rlv, rlr) = splay(left, (rll, rlv, rlr));
        let l_v_rll = node(l, v, rll);
        let rlr_rv_rr = node(rlr, rv, rr);
        (l_v_rll, rlv, rlr_rv_rr);
      }
    | _ => failwith("impossible fallthrough: splay t");
  };

  // returns (l, v), with the interpretation of (l, v, Leaf)
  let rec splay_largest =
    fun
    | (l, v, Leaf) => (l, v)
    | (l, v, Node(rl, rv, Leaf)) => {
        let l_v_rl = node(l, v, rl);
        (l_v_rl, rv);
      }
    // zag-zag
    | (l, v, Node(rl, rv, Node(rrl, rrv, rrr))) => {
        let (rrl, rrv) = splay_largest((rrl, rrv, rrr));
        let l_v_rl = node(l, v, rl);
        let l_v_rl_rv_rrl = node(l_v_rl, rv, rrl);
        (l_v_rl_rv_rrl, rrv);
      };

  let join: ((t('a), t('a))) => t('a) =
    fun
    | (Leaf, t)
    | (t, Leaf) => t
    | (Node(ll, lv, lr), r) => {
        let (l, v) = splay_largest((ll, lv, lr));
        let t = node(l, v, r);
        t;
      };

  let rec insert_t = (entry: 'a, left: Order.t, right: Order.t) =>
    fun
    | Leaf => {
        let info = {
          entry,
          left,
          right,
          max_right: right,
        };
        (Leaf, info, Leaf);
      }
    // already present
    | Node(l, v, r) when eq(left, v.left) => (l, v, r)
    | Node(l, v, r) when lt(left, v.left) => {
        let (ll, lv, lr) = insert_t(entry, left, right, l);
        let ll_lv_lr = node(ll, lv, lr);
        (ll_lv_lr, v, r);
      }
    | Node(l, v, r) when gt(left, v.left) => {
        let (rl, rv, rr) = insert_t(entry, left, right, r);
        let rl_rv_rr = node(rl, rv, rr);
        (l, v, rl_rv_rr);
      }
    | _ => failwith("impossible fallthrough: splay t");

  let insert = (entry: 'a, left: Order.t, right: Order.t, t: t('a)) => {
    let (l, v, r) = insert_t(entry, left, right, t);
    let (l, v, r) = splay(left, (l, v, r));
    node(l, v, r);
  };

  let delete = (left: Order.t) =>
    fun
    | Leaf => Leaf
    | Node(l, v, r) => {
        let (l, v, r) = splay(left, (l, v, r));
        // only delete if [left] appears in the t (and therefore is now at the root)
        if (eq(v.left, left)) {
          join((l, r));
        } else {
          node(l, v, r);
        };
      };

  let rec find_tightest: ((Order.t, Order.t), t('a)) => option(info('a)) =
    ((left, right): (Order.t, Order.t)) =>
      fun
      | Leaf => None
      // if all the right endpoints are too low, return None
      | Node(_, v, _) when !lt(right, v.max_right) => None
      // if v's left endpoint is too high, recurse left
      | Node(l, v, _) when !gt(left, v.left) =>
        find_tightest((left, right), l)
      // otherwise
      // v.left < left < right < v.max_right
      | Node(l, v, r) => {
          // first check the right subtree, which contains the tightest intervals
          switch (find_tightest((left, right), r)) {
          | Some(v) => Some(v)
          // if that fails, check v
          | None when lt(right, v.right) => Some(v)
          // if that fails, recurse left
          | None => find_tightest((left, right), l)
          };
        };

  let splay_tightest:
    ((Order.t, Order.t), t('a)) => option((info('a), t('a))) =
    (left, right) =>
      switch (find_tightest(left, right)) {
      | None => None
      | Some(i) =>
        let (l, v, r) = splay(i.left, unnode(right));
        Some((i, node(l, v, r)));
      };

  // precondition: left < right
  // finds the entry of the node value v in the t such that:
  // 1. v.left < left < right < v.right
  // 2. v is the tightest with this property - it is the smallest interval (each pair of intervals in the t should be either disjoint or one strictly contains the other)
  let rec find_tightest_container: ((Order.t, Order.t), t('a)) => option('a) =
    ((left, right): (Order.t, Order.t)) =>
      fun
      | Leaf => None
      // if all the right endpoints are too low, return None
      | Node(_, v, _) when !lt(right, v.max_right) => None
      // if v's left endpoint is too high, recurse left
      | Node(l, v, _) when !gt(left, v.left) =>
        find_tightest_container((left, right), l)
      // otherwise
      // v.left < left < right < v.max_right
      | Node(l, v, r) => {
          // first check the right subtree, which contains the tightest intervals
          switch (find_tightest_container((left, right), r)) {
          | Some(v) => Some(v)
          // if that fails, check v
          | None when lt(right, v.right) => Some(v.entry)
          // if that fails, recurse left
          | None => find_tightest_container((left, right), l)
          };
        };

  // guarantees either:
  // 1. the new root is the greatest element that is less than left
  // or 2. all elements are greater than left
  let rec splay_largest_lt = (left: Order.t) => {
    fun
    // not found, case 2
    | (Leaf, v, r) when lt(left, v.left) => (Leaf, v, r)
    // not found, case 2
    | (Node(Leaf, lv, lr), v, r)
        when /*lt(left, v.left) &&*/ lt(left, lv.left) => {
        let lr_v_r = node(lr, v, r);
        (Leaf, lv, lr_v_r);
      }
    // zig-zig
    | (Node(Node(lll, llv, llr), lv, lr), v, r)
        when /*lt(left, v.left) &&*/ lt(left, lv.left) => {
        let (lll, llv, llr) = splay_largest_lt(left, (lll, llv, llr));
        let lr_v_r = node(lr, v, r);
        let llr_lv_lr_v_r = node(llr, lv, lr_v_r);
        (lll, llv, llr_lv_lr_v_r);
      }
    // not found, case 1
    | (Node(ll, lv, Leaf), v, r) when lt(left, v.left) && gt(left, lv.left) => {
        let leaf_v_r = node(Leaf, v, r);
        (ll, lv, leaf_v_r);
      }
    // zig-zag
    | (Node(ll, lv, Node(lrl, lrv, lrr)), v, r)
        when lt(left, v.left) && gt(left, lv.left) => {
        let (lrl, lrv, lrr) = splay_largest_lt(left, (lrl, lrv, lrr));
        if (lt(lrv.left, left)) {
          // recursive case 1, return case 1
          let ll_lr_lrl = node(ll, lv, lrl);
          let lrr_v_r = node(lrr, v, r);
          (ll_lr_lrl, lrv, lrr_v_r);
        } else {
          // recursive case 2, return case 1
          let lrl_lrv_lrr = node(lrl, lrv, lrr);
          (ll, lv, lrl_lrv_lrr);
        };
      }
    // not found, case 1
    | (l, v, Leaf) when gt(left, v.left) => (l, v, Leaf)
    // not found, case 1
    | (l, v, Node(rl, rv, Leaf))
        when /*gt(left, v.left) &&*/ gt(left, rv.left) => {
        let l_v_rl = node(l, v, rl);
        (l_v_rl, rv, Leaf);
      }
    // zag-zag
    | (l, v, Node(rl, rv, Node(rrl, rrv, rrr)))
        when /*gt(left, v.left) &&*/ gt(left, rv.left) => {
        let (rrl, rrv, rrr) = splay_largest_lt(left, (rrl, rrv, rrr));
        if (lt(rrv.left, left)) {
          // recursive case 1, return case 1
          let l_v_rl = node(l, v, rl);
          let l_v_rl_rv_rrl = node(l_v_rl, rv, rrl);
          (l_v_rl_rv_rrl, rrv, rrr);
        } else {
          // recursive case 2, return case 1
          let l_v_rl = node(l, v, rl);
          let rrl_rrv_rrr = node(rrl, rrv, rrr);
          (l_v_rl, rv, rrl_rrv_rrr);
        };
      }
    // not found, case 1
    | (l, v, Node(Leaf, rv, rr)) when gt(left, v.left) && lt(left, rv.left) => {
        let leaf_rv_rr = node(Leaf, rv, rr);
        (l, v, leaf_rv_rr);
      }
    | (l, v, Node(Node(rll, rlv, rlr), rv, rr))
        when gt(left, v.left) && lt(left, rv.left) => {
        let (rll, rlv, rlr) = splay_largest_lt(left, (rll, rlv, rlr));
        if (lt(rlv.left, left)) {
          // recursive case 1, return case 1
          let l_v_rll = node(l, v, rll);
          let rlr_rv_rr = node(rlr, rv, rr);
          (l_v_rll, rlv, rlr_rv_rr);
        } else {
          // recursive case 2, return case 1
          let rll_rlv_rlr = node(rll, rlv, rlr);
          let rll_rlv_rlr_rv_rr = node(rll_rlv_rlr, rv, rr);
          (l, v, rll_rlv_rlr_rv_rr);
        };
      }
    | _ => failwith("impossible fallthrough: splay_largest_lt");
  };

  let split = (boundary: Order.t): (t('a) => (t('a), t('a))) =>
    fun
    | Leaf => (Leaf, Leaf)
    | Node(l, v, r) => {
        let (l, v, r) = splay_largest_lt(boundary, (l, v, r));
        // either l < v < boundary < r
        // or boundary < l < v < r
        if (lt(v.left, boundary)) {
          let l_v_leaf = node(l, v, Leaf);
          (l_v_leaf, r);
        } else {
          let l_v_r = node(l, v, r);
          (Leaf, l_v_r);
        };
      };

  // the input Order.t elements can be assumed not to appear anywhere in the tree
  let excise_interval =
      ((left, right): (Order.t, Order.t), t: t('a)): (t('a), t('a)) => {
    assert_order_invariant(t);
    let (t_lt, t_geq) = split(left, t);
    let (t_in, t_gt) = split(right, t_geq);
    // print_endline("lt: " ++ string_of_int(List.length(list_of_t(t_lt))));
    // print_endline("in: " ++ string_of_int(List.length(list_of_t(t_in))));
    // print_endline("gt: " ++ string_of_int(List.length(list_of_t(t_gt))));
    (join((t_lt, t_gt)), t_in);
  };

  let rec union: ((t('a), t('a))) => t('a) =
    fun
    | (Leaf, t)
    | (t, Leaf) => t
    | (Node(ll, lv, lr), Node(rl, rv, rr)) => {
        let (ll, lr) = split(rv.left, Node(ll, lv, lr));
        let l = union((ll, rl));
        let r = union((lr, rr));
        let t = node(l, rv, r);
        // assert_order_invariant(t);
        t;
      };
};
