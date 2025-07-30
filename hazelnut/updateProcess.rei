open State;

type stepped =
  | Settled
  | Stepped;

let update_step: Istate.t => stepped;
let all_update_steps: Istate.t => unit;
