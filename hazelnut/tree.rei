open Order;

module Tree: {
  type info('a) = {
    entry: 'a,
    left: Order.t,
    right: Order.t,
    mutable max_right: Order.t,
  };

  type t('a) =
    | Leaf
    | Node(t('a), info('a), t('a));

  let empty: t('a);
  let insert: ('a, Order.t, Order.t, t('a)) => t('a);
  let delete: (Order.t, t('a)) => t('a);
  let find_tightest_container: (Order.t, t('a)) => option('a);
};
