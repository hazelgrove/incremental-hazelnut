open Hazelnut_lib.Order;
open Hazelnut_lib.Tree;

let order_testable =
  Alcotest.testable(
    // Pretty-printer of Order.t
    (formatter, to_print) =>
      Sexplib0.Sexp.pp_hum(formatter, Order.sexp_of_t(to_print)),
    // Equality test of Order.t
    (a, b) => Order.eq(a, b),
  );

// The ancestry splay tree is ordered by l endpoint of the interval.
let rec assert_order_invariant: Tree.t('a) => unit =
  fun
  | Leaf => ()
  | Node(l, info, right) => {
      // Left comparison
      switch (l) {
      | Leaf => ()

      | Node(_, l_info, _) =>
        if (Order.lt(info.left, l_info.left)) {
          // Warning: sexp_of_t of Order is currently unimplemented.
          Alcotest.failf(
            format_of_string(
              "BST Order Invariant Violated: %s is to the left of %s, but is greater.",
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(l_info.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(info.left)),
          );
        }
      };

      // Left subtree
      assert_order_invariant(l);

      // Right comparison
      switch (right) {
      | Leaf => ()

      | Node(_, right_info, _) =>
        if (Order.gt(info.left, right_info.left)) {
          // Warning: sexp_of_t of Order is currently unimplemented.
          Alcotest.failf(
            format_of_string(
              "BST Order Invariant Violated: %s is to the right of %s, but is lesser.",
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(right_info.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(info.left)),
          );
        }
      };
      // Right subtree
      assert_order_invariant(right);
    };

// The ancestry splay tree's nodes contain the maximum right interval endpoint
// among all children.
let rec assert_max_right: Tree.t('a) => option(Order.t) =
  fun
  | Leaf => None
  | Node(l, info, r) => {
      let max_l = assert_max_right(l);
      let max_right = assert_max_right(r);

      let expected_B =
        switch (max_l, max_right) {
        | (None, None) => info.right
        | (None, Some(r)) => Order.max(info.right, r)
        | (Some(l), None) => Order.max(info.right, l)
        | (Some(l), Some(r)) => Order.max(info.right, Order.max(l, r))
        };

      Alcotest.check(
        order_testable,
        "Max right is not maximum right endpoint of self and children!",
        expected_B,
        info.max_right,
      );

      Some(info.max_right);
    };

type tree = Tree.t(int);
let test_splay_1 = () => {
  let a = Order.create();
  let l = List.init(15, _ => Order.add_next(a));
  let l = [a, ...List.rev(l)];
  let t: tree = Tree.empty;
  let t: tree = Tree.insert(0, List.nth(l, 0), List.nth(l, 1), t);
  let t: tree = Tree.insert(1, List.nth(l, 4), List.nth(l, 5), t);
  let t: tree = Tree.insert(2, List.nth(l, 2), List.nth(l, 3), t);
  let t: tree = Tree.insert(3, List.nth(l, 8), List.nth(l, 9), t);
  let t: tree = Tree.insert(4, List.nth(l, 7), List.nth(l, 10), t);
  let _ = assert_max_right(t);
  let _ = assert_order_invariant(t);
  ();
};

let test_splay_2 = () => {
  let a = Order.create();
  let l = List.init(15, _ => Order.add_next(a));
  let l = [a, ...List.rev(l)];
  let t: tree = Tree.empty;
  let t: tree = Tree.insert(0, List.nth(l, 0), List.nth(l, 1), t);
  let t: tree = Tree.insert(1, List.nth(l, 5), List.nth(l, 8), t);
  let t: tree = Tree.insert(2, List.nth(l, 3), List.nth(l, 4), t);
  let t: tree = Tree.insert(3, List.nth(l, 10), List.nth(l, 11), t);
  let t: tree = Tree.insert(4, List.nth(l, 6), List.nth(l, 7), t);
  let _ = assert_max_right(t);
  let _ = assert_order_invariant(t);
  let interval = (List.nth(l, 2), List.nth(l, 9));
  // let (t11, t12) = Tree.split(fst(interval), t);
  // print_endline(string_of_int(List.length(Tree.list_of_t(t11))));
  // print_endline(string_of_int(List.length(Tree.list_of_t(t12))));
  // let (t21, t22) = Tree.split(snd(interval), t12);
  // print_endline(string_of_int(List.length(Tree.list_of_t(t21))));
  // print_endline(string_of_int(List.length(Tree.list_of_t(t22))));
  let (t1, t2): (tree, tree) = Tree.excise_interval(interval, t);
  let _ = assert_max_right(t1);
  let _ = assert_order_invariant(t1);
  let _ = assert_max_right(t2);
  let _ = assert_order_invariant(t2);
  // print_endline(string_of_int(List.length(Tree.list_of_t(t1))));
  // print_endline(string_of_int(List.length(Tree.list_of_t(t2))));
  assert(List.length(Tree.list_of_t(t1)) == 2);
  assert(List.length(Tree.list_of_t(t2)) == 3);
};

let splay_tests = [
  ("test splay 1", `Quick, test_splay_1),
  ("test splay 2", `Quick, test_splay_2),
];
