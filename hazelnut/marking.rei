// open Hazelnut;
open Incremental;

type bareExp;
type markedExp;
let erase_upper: Iexp.upper => bareExp;
let performance_mark: bareExp => unit;

let marked_correctly: Iexp.upper => option(Iexp.upper);
