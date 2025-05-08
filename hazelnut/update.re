open Typ;
open Term;
open UpdateQueue;
// open Tree;
open State;
open Statics;

type stepped =
  | Settled
  | Stepped;

let typs_of_children = (children: list(Term.t)): list(Typ.t) => {
  let typ_of_child = (child: Term.t): option(Typ.t) => {
    switch (child.content) {
    | Typ(_, typ_data) => Some(typ_data.pure_typ)
    | Pat(_)
    | Exp(_) => None
    };
  };
  List.filter_map(typ_of_child, children);
};

// let pure_typs_of_children = (children: list(Term.t)): list(Typ.t) => {
//   let pure_typ_of_child = (child: Term.t): Typ.t => {
//     switch (child.content) {
//     | Typ(_, typ_data) => typ_data.pure_typ
//     | Pat(_)
//     | Exp(_) => failwith("unreachable")
//     };
//   };
//   List.map(pure_typ_of_child, children);
// };

let syns_of_children = (children: list(Term.t)): list(option(Typ.t)) => {
  let syn_of_child = (child: Term.t): option(option(Typ.t)) => {
    switch (child.content) {
    | Exp(_, exp_data) => Some(fst(exp_data.syn))
    | Pat(_)
    | Typ(_) => None
    };
  };
  List.filter_map(syn_of_child, children);
};
let set_anas_of_children =
    (anas: list(option(Typ.t)), children: list(Term.t)) => {
  List.flatten(List.map2(UpdateQueue.update_ana, children, anas));
};

let update_step = (state: State.t): stepped => {
  let propagate_term = (term: Term.t, queue): unit => {
    switch (term.content) {
    | Typ(constructor, typ_data) =>
      let pure_typ_children = typs_of_children(term.children);
      typ_data.pure_typ = (
        switch (constructor) {
        | Hole => Hole
        | Arrow =>
          Arrow(first(pure_typ_children), second(pure_typ_children))
        }
      );
      let update_list = [Update.NewTyp(fst(Option.get(term.parent)))];
      UpdateQueue.update_push_list(update_list, queue);
    | Exp(constructor, exp_data) =>
      let propagate_in = {
        constructor,
        typs: typs_of_children(term.children),
        ana: fst(Term.get_ana(term)),
        syns: syns_of_children(term.children),
      };
      let propagate_out = propagate_exp(propagate_in);
      let {syn, anas, marks, mark_consistent} = propagate_out;
      let syn_update = UpdateQueue.update_syn(term, syn);
      let ana_updates = set_anas_of_children(anas, term.children);
      term.marks = marks;
      exp_data.mark_consistent = mark_consistent;
      let update_list = syn_update @ ana_updates;
      UpdateQueue.update_push_list(update_list, queue);
    | Pat(_) => failwith("unrecognized update step")
    };
  };
  let apply_update = (update: Update.t, queue): unit => {
    switch (update) {
    | NewAna(term) => propagate_term(term, queue)
    | NewSyn(child) =>
      Option.iter(x => propagate_term(fst(x), queue), child.parent)
    | NewTyp(child) =>
      Option.iter(x => propagate_term(fst(x), queue), child.parent)
    };
  };
  switch (UpdateQueue.update_pop(state.queue)) {
  | None => Settled
  | Some(update) =>
    apply_update(update, state.queue);
    Stepped;
  };
};

let rec all_update_steps = (s: State.t): unit =>
  switch (update_step(s)) {
  | Settled => ()
  | Stepped => all_update_steps(s)
  };
