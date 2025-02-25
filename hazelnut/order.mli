open Sexplib0

module Order : sig
  type parent
  type t
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
  val null : t
  val create : unit -> t
  val is_valid : t -> bool
  val compare : t -> t -> int
  val add_next : t -> t
  val splice : ?inclusive:bool -> t -> t -> unit
  val set_invalidator : t -> (t -> unit) -> unit
  val reset_invalidator : t -> unit
end