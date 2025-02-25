open Hazelnut;
open Incremental;
open UpdateQueue;
open State;

let update_step = (s: Istate.t): option(Istate.t) => {
  print_endline(
    string_of_int(List.length(UpdateQueue.list_of_t(s.q))) ++ " updates.",
  );

  let apply_update = (update: Update.t, q) => {
    switch (update) {
    | NewSyn(e) =>
      switch (e.parent) {
      | Deleted // => failwith("no stepping in deleted terms!!")
      | Root(_) =>
        //UPDATE: TopStep
        print_endline("TopStep");
        {...s, q};
      | Lower(parent) =>
        switch (parent.upper.middle) {
        | Ap(e1, m, e2) when e1.child === e =>
          // UPDATE: StepAp
          print_endline("StepAp");
          let (t_in, t_out, m') = matched_arrow_typ_opt(e.syn);
          e2.ana = t_in;
          parent.upper.syn = t_out;
          m.contents = m';
          e1.marked = Unmarked;
          let update_list = [
            Update.NewAna(Lower(e2)),
            Update.NewSyn(parent.upper),
          ];
          {...s, q: UpdateQueue.update_push_list(update_list, q)};
        | Lam(_, t, _, _, body, _) when Option.is_none(parent.ana) =>
          // UPDATE: StepSynFun
          print_endline("StepSynFun");
          parent.upper.syn =
            arrow_unless(t.contents, body.child.syn, parent.ana);
          body.marked = Unmarked;
          let update_list = [Update.NewSyn(parent.upper)];
          {...s, q: UpdateQueue.update_push_list(update_list, q)};
        | _ when Option.is_some(parent.ana) =>
          // UPDATE: StepSynConsist
          print_endline("StepSynConsist");
          parent.marked = type_consistent_opt(e.syn, parent.ana);
          {...s, q};
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
        // UPDATE: StepAnaFun
        print_endline("StepAnaFun");
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
        {...s, q: UpdateQueue.update_push_list(update_list, q)};
      | _ =>
        // This case must come after the above case. Relies on the term being subsumable.
        // UPDATE: StepAnaConsist
        print_endline("StepAnaConsist");
        mark_parent(type_consistent_opt(child.syn, ana));
        {...s, q};
      };
    | NewAnn(e) =>
      // UPDATE: StepAnnFun
      print_endline("StepAnnFun");
      switch (e.middle) {
      | Lam(_, t, _, _, _, bound_vars) =>
        let update = var => var_syn(var, t.contents);
        let _ = List.map(update, bound_vars.contents);
        let update_list =
          [Update.NewAna(e.parent)]  // TODO: check if e.parent is deleted.
          @ List.map(var => Update.NewSyn(var), bound_vars.contents);
        {...s, q: UpdateQueue.update_push_list(update_list, q)};
      | _ => failwith("NewAnn on non-lam")
      };
    | NewAsc(e) =>
      // UPDATE: StepAsc
      print_endline("StepAsc");
      switch (e.middle) {
      | Asc(low, asc) =>
        e.syn = Some(asc.contents);
        low.ana = Some(asc.contents);
        let update_list = [Update.NewAna(Lower(low)), Update.NewSyn(e)];
        {...s, q: UpdateQueue.update_push_list(update_list, q)};
      | _ => failwith("NewAsc on non-asc")
      };
    };
  };

  switch (UpdateQueue.update_pop(s.q)) {
  | Empty => None
  | Flushed(q) => Some({...s, q})
  | Pops(update, q) => Some(apply_update(update, q))
  };
};

let rec all_update_steps = (s: Istate.t): Istate.t =>
  switch (update_step(s)) {
  | None => s
  | Some(s') => all_update_steps(s')
  };
