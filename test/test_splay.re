open Hazelnut_lib.Order;
open Hazelnut_lib.Tree;

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
              "BST Order Invariant Violated: %s is to the left of %s, but is greater."
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(left_data.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(data.left))
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
              "BST Order Invariant Violated: %s is to the right of %s, but is lesser."
            ),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(right_data.left)),
            Sexplib0.Sexp.to_string_hum(Order.sexp_of_t(data.left))
          );

        }

    };
    // Right subtree
    assert_order_invariant(right);
  }
