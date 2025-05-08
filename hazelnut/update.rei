open State;

type stepped =
  | Settled
  | Stepped;

let update_step: State.t => stepped;
let all_update_steps: State.t => unit;
