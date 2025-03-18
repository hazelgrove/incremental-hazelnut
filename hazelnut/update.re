open Hazelnut;
open Incremental;
open UpdateQueue;
open Tree;
open State;

type stepped =
  | Settled
  | Stepped;

let update_step = (state: Istate.t): stepped => {
  print_endline(
    string_of_int(List.length(UpdateQueue.list_of_t(state.ephemeral.q)))
    ++ " updates.",
  );

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
          e2.ana = t_in;
          parent.upper.syn = t_out;
          m.contents = m';
          e1.marked = Unmarked;
          let update_list = [
            Update.NewAna(Lower(e2)),
            Update.NewSyn(parent.upper),
          ];
          UpdateQueue.update_push_list(update_list, q);
        | Lam(_, t, _, _, body, _) when Option.is_none(parent.ana) =>
          //print_endine("STEP: StepSynFun");
          parent.upper.syn =
            arrow_unless(t.contents, body.child.syn, parent.ana);
          body.marked = Unmarked;
          let update_list = [Update.NewSyn(parent.upper)];
          UpdateQueue.update_push_list(update_list, q);
        | Pair(e1, e2, _) when Option.is_none(parent.ana) =>
          parent.upper.syn =
            product_unless(e1.child.syn, e2.child.syn, parent.ana);
          parent.marked = Unmarked; // Removes the mark from the originating child
          let update_list = [Update.NewSyn(parent.upper)];
          UpdateQueue.update_push_list(update_list, q);
        | Proj(prod_side, e, m) =>
          let (t_side_body, m_all_body) =
            matched_proj_typ_opt(prod_side, e.child.syn);
          m.contents = m_all_body;
          parent.upper.syn = t_side_body;
          let update_list = [Update.NewSyn(parent.upper)];
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
        body.ana = t_out;
        child.syn = arrow_unless(t_ann.contents, body.child.syn, ana);
        mark_parent(Unmarked);
        let update_list = [
          Update.NewAna(Lower(body)),
          Update.NewSyn(child),
        ];
        UpdateQueue.update_push_list(update_list, q);
      | Pair(e1, e2, m) =>
        let (t1, t2, m_ana') = matched_product_typ_opt(ana);
        m.contents = m_ana';
        e1.ana = t1;
        e2.ana = t2;
        child.syn = product_unless(e1.child.syn, e2.child.syn, ana);
        let update_list = [
          Update.NewAna(Lower(e1)),
          Update.NewAna(Lower(e2)),
          Update.NewSyn(child),
        ];
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
        let update = var => var_syn(var, t.contents);
        Tree.iter(update, bound_vars.contents);
        let bound_vars_list = Tree.list_of_t(bound_vars.contents);
        let update_list =
          [Update.NewAna(e.parent)]  // TODO: check if e.parent is deleted.
          @ List.map(var => Update.NewSyn(var), bound_vars_list);
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewAnn on non-lam")
      }
    | NewAsc(e) =>
      //print_endine("STEP: StepAsc");
      switch (e.middle) {
      | Asc(low, asc) =>
        e.syn = Some(asc.contents);
        low.ana = Some(asc.contents);
        let update_list = [Update.NewAna(Lower(low)), Update.NewSyn(e)];
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewAsc on non-asc")
      }
    | NewListRec(e) =>
      // print_endline("STEP: StepListRec");
      switch (e.middle) {
      | ListRec(t) =>
        e.syn =
          Some(
            Arrow(
              t.contents,
              Arrow(
                Arrow(Num, Arrow(t.contents, t.contents)),
                Arrow(List, t.contents),
              ),
            ),
          );
        let update_list = [Update.NewSyn(e)];
        UpdateQueue.update_push_list(update_list, q);
      | _ => failwith("NewListRec on non ListRec")
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
