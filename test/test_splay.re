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

// The ancestry splay tree is ordered by left endpoint of the interval.
let rec assert_order_invariant: Tree.t('a) => unit =
  fun
  | Leaf => ()
  | Node(left, data, right) => {
      // Left comparison
      switch (left) {
      | Leaf => ()

      | Node(_, left_data, _) =>
        if (left_data.left > data.left) {
          // Warning: sexp_of_t of Order is currently unimplemented.
          Alcotest.failf(
            format_of_string(
              "BST Order Invariant Violated: %s is to the left of %s, but is greater.",
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(left_data.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(data.left)),
          );
        }
      };

      // Left subtree
      assert_order_invariant(left);

      // Right comparison
      switch (right) {
      | Leaf => ()

      | Node(_, right_data, _) =>
        if (right_data.left < data.left) {
          // Warning: sexp_of_t of Order is currently unimplemented.
          Alcotest.failf(
            format_of_string(
              "BST Order Invariant Violated: %s is to the right of %s, but is lesser.",
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(right_data.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(data.left)),
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
      let max_left = assert_max_right(l);
      let max_right = assert_max_right(r);

      let expected_B =
        switch (max_left, max_right) {
        | (None, None) => info.right
        | (None, Some(r)) => Order.max(info.right, r)
        | (Some(l), None) => Order.max(info.right, l)
        | (Some(l), Some(r)) => Order.max(info.right, Order.max(l, r))
        };

      print_endline(string_of_bool(Order.is_valid(expected_B)));
      print_endline(string_of_bool(Order.is_valid(info.max_right)));

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
  let _ = assert_max_right(t);
  let _ = assert_order_invariant(t);
  ();
};

let splay_tests = [("test splay 1", `Quick, test_splay_1)];
