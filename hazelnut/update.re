open Hazelnut;
open Incremental;
open UpdateQueue;
open Tree;
open State;

type stepped =
  | Settled
  | Stepped;

let _update_ana_dum =
    (lower: Iexp.lower, t_new: option(Htyp.t)): list(Update.t) => {
  lower.ana = t_new;
  [Update.NewAna(Lower(lower))];
};

let _update_syn_dum =
    (upper: Iexp.upper, t_new: option(Htyp.t)): list(Update.t) => {
  upper.syn = t_new;
  [Update.NewSyn(upper)];
};

let var_syn = (e: Iexp.upper, syn: Htyp.t): list(Update.t) => {
  switch (e.middle) {
  | Var(_) => UpdateQueue.update_syn(e, Some(syn))
  | _ => failwith("var_syn called on non-var")
  };
};

let update_step = (state: Istate.t): stepped => {
  // print_endline(
  //   string_of_int(List.length(UpdateQueue.list_of_t(state.ephemeral.q)))
  //   ++ " updates.",
  // );

  // switch (List.nth(UpdateQueue.list_of_t(state.ephemeral.q), 0)) {
  // | NewListRec(_) => print_endline("found0")
  // | _ => ()
  // };

  // switch (List.nth(UpdateQueue.list_of_t(state.ephemeral.q), 1)) {
  // | NewListRec(_) => print_endline("found1")
  // | _ => ()
  // };

  let apply_update = (update: Update.t, q): unit => {
    switch (update) {
    | NewSyn(e) =>
      switch (e.parent) {
      | Deleted => failwith("step in deleted term")
      | Root(_) =>
        // print_endline("STEP: TopStep")
        ()
      | Lower(parent) =>
        switch (parent.upper.middle) {
        | Ap(e1, m, e2) when e1.child === e =>
          //print_endine("STEP: StepAp");
          let (t_in, t_out, m') = matched_arrow_typ_opt(e.syn);
          let e2_update = UpdateQueue.update_ana(e2, t_in);
          let parent_update = UpdateQueue.update_syn(parent.upper, t_out);
          m.contents = m';
          e1.marked = Unmarked;
          let update_list = e2_update @ parent_update;
          UpdateQueue.update_push_list(update_list, q);
        | Lam(_, t, _, _, body, _) when Option.is_none(parent.ana) =>
          //print_endine("STEP: StepSynFun");
          let parent_update =
            UpdateQueue.update_syn(
              parent.upper,
              arrow_unless(t.contents, body.child.syn, parent.ana),
            );
          body.marked = Unmarked;
          let update_list = parent_update;
          UpdateQueue.update_push_list(update_list, q);
        | Pair(e1, e2, _) when Option.is_none(parent.ana) =>
          let parent_update =
            UpdateQueue.update_syn(
              parent.upper,
              product_unless(e1.child.syn, e2.child.syn, parent.ana),
            );
          parent.marked = Unmarked; // Removes the mark from the originating child
          let update_list = parent_update;
          UpdateQueue.update_push_list(update_list, q);
        | Proj(prod_side, e, m) =>
          let (t_side_body, m_all_body) =
            matched_proj_typ_opt(prod_side, e.child.syn);
          m.contents = m_all_body;
          let parent_update =
            UpdateQueue.update_syn(parent.upper, t_side_body);
          let update_list = parent_update;
          UpdateQueue.update_push_list(update_list, q);
        | _ when Option.is_some(parent.ana) =>
          //print_endine("STEP: StepSynConsist");
          parent.marked = type_consistent_opt(e.syn, parent.ana)
        | _ => failwith("unrecognized update step")
        }
      }
    | NewAna(parent) =>
      let child = child_of_parent(parent);
      let ana =
        switch (parent) {
        | Lower(lower) => lower.ana
        | _ => None
        };
      let mark_parent = m =>
        switch (parent) {
        | Lower(lower) => lower.marked = m
        | _ => ()
        };
      switch (child.middle) {
      | Lam(_, t_ann, m_ana, m_ann, body, _) =>
        //print_endine("STEP: StepAnaFun");
        let (t_in, t_out, m_ana') = matched_arrow_typ_opt(ana);
        let m_ann' = type_consistent_opt(Some(t_ann.contents), t_in);
        m_ana.contents = m_ana';
        m_ann.contents = m_ann';
        let body_update = UpdateQueue.update_ana(body, t_out);
        let syn_update =
          UpdateQueue.update_syn(
            child,
            arrow_unless(t_ann.contents, body.child.syn, ana),
          );
        mark_parent(Unmarked);
        let update_list = body_update @ syn_update;
        UpdateQueue.update_push_list(update_list, q);
      | Pair(e1, e2, m) =>
        let (t1, t2, m_ana') = matched_product_typ_opt(ana);
        m.contents = m_ana';
        let e1_update = UpdateQueue.update_ana(e1, t1);
        let e2_update = UpdateQueue.update_ana(e2, t2);
        let syn_update =
          UpdateQueue.update_syn(
            child,
            product_unless(e1.child.syn, e2.child.syn, ana),
          );
        let update_list = e1_update @ e2_update @ syn_update;
        UpdateQueue.update_push_list(update_list, q);
      | _ =>
        // This case must come after the above case. Relies on the term being subsumable.
        //print_endine("STEP: StepAnaConsist");
        mark_parent(type_consistent_opt(child.syn, ana))
      };
    | NewAnn(e) =>
      //print_endine("STEP: StepAnnFun");
      switch (e.middle) {
      | Lam(_, t, _, _, _, bound_vars) =>
        let var_list = Tree.list_of_t(bound_vars.contents);
        let update = var => var_syn(var, t.contents);
        let updates = List.concat_map(update, var_list);
        let update_list = [Update.NewAna(e.parent)] @ updates;
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewAnn on non-lam")
      }
    | NewAsc(e) =>
      //print_endine("STEP: StepAsc");
      switch (e.middle) {
      | Asc(low, asc) =>
        let syn_update = UpdateQueue.update_syn(e, Some(asc.contents));
        let ana_update = UpdateQueue.update_ana(low, Some(asc.contents));
        let update_list = ana_update @ syn_update;
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewAsc on non-asc")
      }
    | NewListRec(e) =>
      // print_endline("STEP: StepListRec");
      switch (e.middle) {
      | ListRec(t) =>
        let syn_type: option(Htyp.t) =
          Some(
            Arrow(
              t.contents,
              Arrow(
                Arrow(Num, Arrow(t.contents, t.contents)),
                Arrow(List, t.contents),
              ),
            ),
          );
        let syn_update = UpdateQueue.update_syn(e, syn_type);
        let update_list = syn_update;
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewListRec on non ListRec")
      }
    | NewY(e) =>
      // print_endline("STEP: StepY");
      switch (e.middle) {
      | Y(t) =>
        let syn_type: option(Htyp.t) =
          Some(
            Arrow(
              Arrow(
                Arrow(t.contents, t.contents),
                Arrow(t.contents, t.contents),
              ),
              Arrow(t.contents, t.contents),
            ),
          );
        let syn_update = UpdateQueue.update_syn(e, syn_type);
        let update_list = syn_update;
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewY on non Y")
      }
    };
  };

  switch (UpdateQueue.update_pop(state.ephemeral.q)) {
  | None => Settled
  | Some(update) =>
    apply_update(update, state.ephemeral.q);
    Stepped;
  };
};

let rec all_update_steps = (s: Istate.t): unit =>
  switch (update_step(s)) {
  | Settled => ()
  | Stepped => all_update_steps(s)
  };
