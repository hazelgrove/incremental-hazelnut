open Actions;

let random_motion = (): Iaction.t => {
  let moves: list(Iaction.t) = [
    MoveUp,
    MoveUp,
    MoveUp,
    MoveDown(One),
    MoveDown(Two),
    MoveDown(Three),
  ];
  List.nth(moves, Random.int(List.length(moves)));
};

let random_motions = () => {
  List.init(Random.int(10), _ => random_motion());
};

let random_edit = (): list(Iaction.t) => {
  let edits: list(list(Iaction.t)) = [
    [Delete],
    // [WrapArrow(One)],
    // [WrapArrow(Two)],
    // [InsertNumType],
    // [InsertNumLit(0)],
    [InsertVar("x")],
    // [InsertVar("y")],
    [WrapPlus(One)],
    // [WrapPlus(Two)],
    // [WrapAp(One)],
    // [WrapAp(Two)],
    // [WrapAsc],
    [WrapLam, MoveDown(One), InsertVar("x"), MoveUp],
    // [WrapLam, MoveDown(One), InsertVar("y"), MoveUp],
    [Unwrap(One)],
    // [Unwrap(Two)],
  ];
  List.nth(edits, Random.int(List.length(edits)));
};

let random_action_segment = () => {
  Random.self_init();
  random_motions() @ random_edit();
};

let random_action_segments = n => {
  let l = List.init(n, _ => random_action_segment());
  l;
};
