open Order;

module Tree: {
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

  let empty: t('a);
  let is_empty: t('a) => bool;
  let iter: ('a => unit, t('a)) => unit;
  let list_of_t: t('a) => list('a);

  let union: ((t('a), t('a))) => t('a);

  let insert: ('a, Order.t, Order.t, t('a)) => t('a);
  let delete: (Order.t, t('a)) => t('a);
  let find_tightest_container: ((Order.t, Order.t), t('a)) => option('a);
  let splay_tightest:
    ((Order.t, Order.t), t('a)) => option((info('a), t('a)));
  let excise_interval: ((Order.t, Order.t), t('a)) => (t('a), t('a));
};
