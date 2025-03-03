open Hazelnut_lib.Order;
open Hazelnut_lib.Tree;

let order_testable =
  Alcotest.testable(
    // Pretty-printer of Order.t
    (formatter, to_print) =>
      Sexplib0.Sexp.pp_hum(formatter, Order.sexp_of_t(to_print)),
    // Equality test of Order.t
    (a, b) => a == b,
  );

// The ancestry splay tree is ordered by left endpoint of the interval.
let rec assert_order_invariant =
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
let rec assert_max_right =
  fun
  | Leaf => None
  | Node(left, data, right) => {
      let max_left = assert_max_right(left);
      let max_right = assert_max_right(right);

      let expected_B = ref(data.right);

      switch (max_left) {
      | None => ()
      | Some(left_B) =>
        if (left_B > expected_B^) {
          expected_B := left_B;
        }
      };

      switch (max_right) {
      | None => ()
      | Some(right_B) =>
        if (right_B > expected_B^) {
          expected_B := right_B;
        }
      };

      Alcotest.check(
        order_testable,
        "Max right is not maximum right endpoint of self and children!",
        expected_B^,
        data.max_right,
      );

      Some(expected_B^);
    };
