open Order;

module Tree: {
  type t('a);

  let empty: t('a);
  let insert: ('a, Order.t, Order.t, t('a)) => t('a);
  let delete: (Order.t, t('a)) => t('a);
  let find_tightest_container: (Order.t, t('a)) => option('a);
};
