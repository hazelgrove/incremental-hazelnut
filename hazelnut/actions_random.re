open Actions;
open State;

let choose_random = l => List.nth(l, Random.int(List.length(l)));

let random_motion = (): Iaction.t => {
  let moves: list(Iaction.t) = [
    MoveUp,
    MoveUp,
    MoveUp,
    MoveDown(One),
    MoveDown(Two),
    MoveDown(Three),
  ];
  choose_random(moves);
};

let random_motions = () => {
  List.init(Random.int(2), _ => random_motion());
};

let random_edit = (no_delete: bool): list(Iaction.t) => {
  let edits: list(list(Iaction.t)) =
    if (no_delete) {
      [
        // [Delete],
        [WrapArrow(One)],
        // [WrapArrow(Two)],
        [WrapProduct(One)],
        // [WrapProduct(Two)],
        [InsertNumType],
        [InsertList],
        [InsertNumLit(0)],
        [InsertVar("x")],
        [InsertVar("y")],
        [WrapPlus(One)],
        // [WrapPlus(Two)],
        [WrapPair(One)],
        // [WrapPair(Two)],
        [WrapProj(Fst)],
        [WrapProj(Snd)],
        [WrapAp(One)],
        // [WrapAp(Two)],
        [WrapAsc],
        [WrapLam, MoveDown(One), InsertVar("x"), MoveUp],
        [WrapLam, MoveDown(One), InsertVar("y"), MoveUp],
        [InsertNil],
        [InsertCons],
        [InsertListRec],
        [InsertY],
        [Unwrap(One)],
        // [Unwrap(Two)],
      ];
    } else {
      [
        [Delete],
        [WrapArrow(One)],
        [WrapArrow(Two)],
        [WrapProduct(One)],
        [WrapProduct(Two)],
        [InsertNumType],
        [InsertList],
        [InsertNumLit(0)],
        [InsertVar("x")],
        [InsertVar("y")],
        [WrapPlus(One)],
        [WrapPlus(Two)],
        [WrapPair(One)],
        [WrapPair(Two)],
        [WrapProj(Fst)],
        [WrapProj(Snd)],
        [WrapAp(One)],
        [WrapAp(Two)],
        [WrapAsc],
        [WrapLam, MoveDown(One), InsertVar("x"), MoveUp],
        [WrapLam, MoveDown(One), InsertVar("y"), MoveUp],
        [InsertNil],
        [InsertCons],
        [InsertListRec],
        [InsertY],
        [Unwrap(One)],
        [Unwrap(Two)],
      ];
    };
  choose_random(edits);
};

let random_action_segment_arg = (no_delete: bool) => {
  Random.self_init();
  random_motions() @ random_edit(no_delete);
};

let random_action_segment = () => random_action_segment_arg(false);

let random_action_segments = (n: int) => {
  let l = List.init(n, _ => random_action_segment());
  l;
};

let random_action_segments_no_delete = (n: int) => {
  let l = List.init(n, _ => random_action_segment_arg(true));
  l;
};

let random_edit_smart = (s: Istate.t) => {
  switch (s.persistent.c) {
  | CursorBind(_) => [
      choose_random(
        [Delete, InsertVar("x"), InsertVar("y")]: list(Iaction.t),
      ),
    ]
  | CursorTyp(_) => [
      choose_random(
        [InsertNumType, WrapArrow(One), WrapArrow(Two)]: list(Iaction.t),
      ),
    ]
  | CursorExp(_) =>
    choose_random(
      [
        [Delete],
        // [InsertNumLit(0)],
        [InsertVar("x")],
        [InsertVar("y")],
        [WrapPlus(One)],
        [WrapPlus(Two)],
        [WrapAp(One)],
        [WrapAp(Two)],
        [WrapAsc],
        [WrapLam],
        [WrapLam, MoveDown(One), InsertVar("x")],
        [WrapLam, MoveDown(One), InsertVar("y")],
        [Unwrap(One)],
        [Unwrap(Two)],
      ]: list(list(Iaction.t)),
    )
  };
};

let random_action_segment_smart = (s: Istate.t) => {
  Random.self_init();
  let motions = random_motions();
  let s' = List.fold_left(apply_action, s, motions);
  let edit = random_edit_smart(s');
  let s'' = List.fold_left(apply_action, s, edit);
  (s'', motions @ edit);
};

let rec random_action_segments_smart_rec = (n, s_acc, rev_acc) =>
  if (n == 0) {
    List.rev(rev_acc);
  } else {
    let (s_acc', segment) = random_action_segment_smart(s_acc);
    random_action_segments_smart_rec(n - 1, s_acc', [segment, ...rev_acc]);
  };

let random_action_segments_smart = n =>
  random_action_segments_smart_rec(n, initial_state(), []);
