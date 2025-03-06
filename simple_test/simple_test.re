open Hazelnut_lib.Actions;
open Hazelnut_lib.Marking;
open Hazelnut_lib.State;
open Hazelnut_lib.Update;
open Hazelnut_lib.Counterexample;
let s = initial_state();
let s' = apply_actions(minimized_5, s);
all_update_steps(s');
switch (marked_correctly(s'.ephemeral.root.root_child)) {
| Some(_) => failwith("marked incorrectly (top test validity)")
| None => print_endline("marked correctly (top test validity)")
};
