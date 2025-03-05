open Actions;

let random_motion = (): Iaction.t => {
  let r = Random.int(6);
  switch (r) {
  | 0
  | 1
  | 2 => MoveUp
  | 3 => MoveDown(One)
  | 4 => MoveDown(Two)
  | 5 => MoveDown(Three)
  | _ => failwith("bad random number")
  };
};

let random_motions = () => {
  List.init(Random.int(13), _ => random_motion());
};

let random_edit = (): list(Iaction.t) => {
  let r = Random.int(11);
  switch (r) {
  | 0 => [Delete]
  | 1 => [WrapArrow(One)]
  | 2 => [InsertNumType]
  | 3 => [InsertNumLit(0)]
  | 4 => [InsertVar("x")]
  | 5 => [InsertVar("y")]
  | 6 => [WrapPlus(One)]
  | 7 => [WrapAp(One)]
  | 8 => [WrapAsc]
  | 9 => [WrapLam, MoveUp, MoveDown(One), InsertVar("x"), MoveUp]
  | 10 => [WrapLam, MoveUp, MoveDown(One), InsertVar("y"), MoveUp]
  | _ => failwith("bad random number")
  };
};

let random_action_segment = () => random_motions() @ random_edit();

let random_action_segments = n => {
  let l = List.init(n, _ => random_action_segment());
  // let s =  string_of_action_list_list(l);
  // write_string_to_file("random_action_" ++ string_of_int(n) ++ ".txt", s);
  l;
};
