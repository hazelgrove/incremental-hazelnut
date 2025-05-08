open Mark;
open Typ;
open Term;
open Side_conditions;

type propagate_exp_in = {
  constructor: Term.exp_constructor,
  typs: list(Typ.t),
  ana: option(Typ.t),
  syns: list(option(Typ.t)),
};

type propagate_exp_out = {
  syn: option(Typ.t),
  anas: list(option(Typ.t)),
  marks: list(Mark.t),
  mark_consistent: Mark.t,
};

// this could be more incremental, but it's tough in this general framework
let propagate_exp = (p: propagate_exp_in): propagate_exp_out => {
  switch (p.constructor) {
  | Var(_) =>
    let syn = Some(List.nth(p.typs, 0));
    let mark_consistent = consistent_opt(syn, p.ana);
    {syn, anas: [], marks: [], mark_consistent};
  | Fun(_) =>
    let ann = List.nth(p.typs, 0);
    // ana
    let (ann_of_ana, ana1, mark1) = matched_arrow_opt(p.ana);
    let mark2 = consistent_opt(Some(ann), ann_of_ana);
    // syn
    let syn1 = List.nth(p.syns, 0);
    let syn = fun_syn(p.ana, ann, syn1);
    let mark_consistent = consistent_opt(syn, p.ana);
    {syn, anas: [ana1], marks: [mark1, mark2], mark_consistent};
  | Ap =>
    let syn1 = List.nth(p.syns, 0);
    let _syn2 = (); //List.nth(p.syns, 1);
    let (ana1, syn, mark1) = matched_arrow_opt(syn1);
    let mark_consistent = consistent_opt(p.ana, syn);
    let ana2 = None;
    {syn, anas: [ana1, ana2], marks: [mark1], mark_consistent};
  | Hole =>
    let syn: option(Typ.t) = Some(Hole);
    let mark_consistent: Mark.t = Unmarked;
    {syn, anas: [], marks: [], mark_consistent};
  | Multihole(n) =>
    let anas = List.init(n, _ => p.ana);
    let syn: option(Typ.t) = Some(Hole);
    let mark_consistent: Mark.t = Unmarked;
    {syn, anas, marks: [], mark_consistent};
  | Multiref(_) =>
    let syn: option(Typ.t) = Some(Hole);
    let mark_consistent: Mark.t = Unmarked;
    {syn, anas: [], marks: [], mark_consistent};
  | Uniref(_) =>
    let syn: option(Typ.t) = Some(Hole);
    let mark_consistent: Mark.t = Unmarked;
    {syn, anas: [], marks: [], mark_consistent};
  };
};
