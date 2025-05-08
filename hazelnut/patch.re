open Id;

module Patch = {
  type constructor =
    | Var(string)
    | Fun(string)
    | Ap;

  type node = (Id.t, constructor);

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
