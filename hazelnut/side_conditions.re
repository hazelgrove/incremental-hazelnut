open Typ;
open Mark;

let matched_arrow = (t: Typ.t): (Typ.t, Typ.t, Mark.t) => {
  switch (t) {
  | Arrow(t1, t2) => (t1, t2, Unmarked)
  | Hole => (Hole, Hole, Unmarked)
  // | _ => (Hole, Hole, Marked)
  };
};

let matched_arrow_opt =
    (t: option(Typ.t)): (option(Typ.t), option(Typ.t), Mark.t) => {
  switch (t) {
  | Some(t) =>
    let (t_in, t_out, m) = matched_arrow(t);
    (Some(t_in), Some(t_out), m);
  | None => (None, None, Unmarked)
  };
};

let rec is_consistent = (t1: Typ.t, t2: Typ.t): bool => {
  switch (t1, t2) {
  | (Hole, _)
  | (_, Hole) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    is_consistent(t11, t21) && is_consistent(t12, t22)
  // | (Num, Num) => true
  // | (Product(t11, t12), Product(t21, t22)) =>
  //   is_consistent(t11, t21) && is_consistent(t12, t22)
  // | _ => false
  };
};

let consistent = (t1: Typ.t, t2: Typ.t): Mark.t => {
  is_consistent(t1, t2) ? Unmarked : Marked;
};

let consistent_opt = (t1: option(Typ.t), t2: option(Typ.t)): Mark.t => {
  switch (t1, t2) {
  | (None, _) => Unmarked
  | (_, None) => Unmarked
  | (Some(t1), Some(t2)) => consistent(t1, t2)
  };
};

let fun_syn =
    (ana: option(Typ.t), ann: Typ.t, syn1: option(Typ.t)): option(Typ.t) => {
  switch (ana, syn1) {
  | (None, None) => None
  | (None, Some(syn1)) => Some(Arrow(ann, syn1))
  | (Some(_), _) => None
  };
};
