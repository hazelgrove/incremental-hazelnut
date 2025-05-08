module Typ = {
  type t =
    | Hole
    | Arrow(t, t);
};
