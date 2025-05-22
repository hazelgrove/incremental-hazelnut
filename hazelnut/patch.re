open Id;

module Patch = {
  type pat_constructor =
    | Var(string);

  type typ_constructor =
    | Arrow;

  type exp_constructor =
    | Var(string)
    | Fun(string)
    | Ap;

  type content =
    | Pat(pat_constructor)
    | Typ(typ_constructor)
    | Exp(exp_constructor);

  type node = (Id.t, content);

  type position = int;

  type location = (node, position);

  type sign =
    | Add
    | Delete;

  type meta =
    | Alexander
    | NotAlexander;

  type t = {
    id: Id.t,
    source: location,
    destination: node,
    sign,
    meta,
  };
};
