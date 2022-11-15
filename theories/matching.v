From Coq Require Import String List Arith Lia.
From minilog Require Import data utils.
Import ListNotations.

(** * Verified Matching Algorithm *)

(** A state of the algorithm is a list of equations to be solved and a current solution.
    Solutions are represented as finite maps from variables to closed terms ([datum])
*)
Record state := {
  equations : list (datum * pattern);
  solution  : @fin_map datum;
}.

(** Intepreting a finite map as a substitution *)
Definition interp (sub : fin_map) : csubstitution :=
  fun x => match get sub x with None => Dcst "" | Some vx => vx end.

(** At every iteration, the algorithm either fails, update the current state,
    or terminates with a solution *)
Inductive status :=
  | Failure
  | Update (st : state)
  | Success (sub : @fin_map datum).

(** Intepreting a finite map as a set of equations *)
Definition map_as_equations (m : @fin_map datum) :=
  map (fun '(x, y) => (y, Pvar x)) m.

(** Intepreting a state as set of equations *)
Definition state_as_equations (st : state) :=
  equations st ++ map_as_equations (solution st).

(** What it means to be a solution to a set of equations *)
Definition satisfy (s : csubstitution) equs :=
  Forall (fun '(x, y) => Matching s x y) equs.

(** Equivalence of two sets of equations *)
Definition equiv equs1 equs2 :=
  forall s, satisfy s equs1 <-> satisfy s equs2.

(** Equivalence of two states *)
Definition state_equiv st1 st2 :=
  equiv (state_as_equations st1) (state_as_equations st2).

(** All bindings of a map are preserved when the map is interpreted as a set of equations *)
Lemma in_map_in_equations:
  forall sol (d : datum) (n : nat), In (n, d) sol -> In (d, Pvar n) (map_as_equations sol).
Proof.
  induction sol as [| [n dat] sol IH]; try easy.
  intros d m [[=->->] | H2]. now left.
  right. now apply IH.
Qed.

(** All equations generated from a map are of the form [(_, Pvar x)] where [x]
    is bound in the map *)
Lemma in_equations_in_map:
  forall dat pat sub,
    In (dat, pat) (map_as_equations sub) -> exists x, pat = Pvar x /\ get sub x <> None.
Proof.
  intros. induction sub as [|[x vx] sub IH].
  - inversion H.
  - simpl in H. destruct H as [[=-><-] | Hin].
    exists x. split; auto. simpl.
    now rewrite Nat.eqb_refl.
    specialize (IH Hin) as [y [Hy1 Hy2]].
    exists y; split; auto.
    simpl. now destruct (x =? y)%nat.
Qed.

(** Reduce the problem of matching 2 lists of terms
    to the problem of solving a list of equations
*)
Fixpoint decompose (l1 : list datum) (l2 : list pattern) :=
  match l1, l2 with
  | [], [] => Some []
  | x::xs, y::ys =>
    do equs <- decompose xs ys;
    Some ((x, y)::equs)
  | _, _ => None
  end.

(** One step of the matching algorithm:
    We start by picking an equation from the worklist.
    If it is a trivial equation, it is deleted and
    the solution is extended accordingly.
    If it is a non trivial equation, we decompose it and
    extend the worklist.
*)
Definition matching_step (st : state) : status :=
  match equations st with
  | [] => Success (solution st)
  | (Dcmp f1 l1, Pcmp f2 l2)::equs =>
    if (f1 =? f2)%string then
      match decompose l1 l2 with
      | Some equs' => Update (Build_state (equs' ++ equs) (solution st))
      | None => Failure
      end
    else Failure
  | (d, Pvar x)::equs =>
    match get (solution st) x with
    | None => Update (Build_state equs ((x, d)::(solution st)))
    | Some vx =>
      if (vx =? d)%datum then Update (Build_state equs (solution st)) else Failure
    end
  end.

Lemma decompose_equiv:
  forall s1 s2 l1 l2 l,
    (s1 =? s2)%string = true ->
    decompose l1 l2 = Some l ->
    equiv l [(Dcmp s1 l1, Pcmp s2 l2)].
Proof.
  intros * ->%String.eqb_eq H sub. 
  induction l2 in l, l1, H, sub |-*.
  - destruct l1; try easy. simpl in *.
    inversion_clear H. now repeat econstructor.
  - destruct l1; try easy. simpl in *.
    destruct (decompose l1 l2) as [l'|] eqn:Heq; try easy.
    simpl in H. inversion H; subst. clear H.
    specialize (IHl2 _ _ Heq sub) as [H1 H2].
    split; intros.
    + inversion_clear H as [| ? ? H3 H4].
      specialize (H1 H4).
      inversion_clear H3.
      inversion_clear H1 as [| ? ? H3 _].
      inversion_clear H3.
      now econstructor.
    + inversion H as [| ? ? H3 _]; subst.
      inversion H3. apply Forall_cons; try easy.
      apply H2. apply Forall_cons; try easy.
      subst. repeat econstructor.
Qed.

Lemma matching_step_equiv:
  forall st1 st2,
    matching_step st1 = Update st2 ->
    state_equiv st1 st2.
Proof.
  intros [equs1 sol1] [equs2 sol2] H.
  induction equs1 as [| [dat1 pat1] equs1 _] in equs2, sol2, H |-*; try easy.
  destruct dat1, pat1; try easy.
  - unfold matching_step in H. simpl in H.
    destruct get eqn:Hget in H;
    try destruct datum_eqb eqn:Hdat in H; try easy.
    + inversion H; subst. clear H. intros sub. split.
      * intros Hsat. inversion_clear Hsat as [| ? ? H1 H2]; subst.
        apply Forall_app in H2 as [H2 H3].
        red. cbn. apply Forall_app. split; auto.
      * intros Hsat. red. cbn. apply Forall_cons; auto.
        apply datum_eqb_eq in Hdat; subst.
        unfold satisfy, state_as_equations in Hsat.
        apply Forall_app in Hsat as [_ H2]. simpl in H2.
        apply get_in in Hget.
        rewrite Forall_forall in H2.
        now specialize (H2 (Dcmp s l, Pvar n) (in_map_in_equations _ _ _ Hget)).
    + inversion H; subst. clear H. intros sub. split.
      * intros Hsat. inversion_clear Hsat as [| ? ? H1 H2].
        apply Forall_app in H2 as [H2 H3].
        red. cbn. apply Forall_app; split; auto.
      * intros Hsat. unfold satisfy in *. cbn in *.
        apply Forall_app in Hsat as [H1 H2]. simpl in *.
        inversion H2 as [|? ? H3 H4]; subst.
        apply Forall_cons; auto.
        apply Forall_app; auto.
  - unfold matching_step in H. simpl in H.
    destruct String.eqb eqn:Hstr in H; try easy.
    inversion H; subst. clear H.
    destruct (decompose l l0) eqn:Hdec; try easy.
    inversion H1; subst. clear H1.
    intros sub. unfold state_as_equations. simpl.
    pose proof (decompose_equiv _ _ _ _ _ Hstr Hdec sub) as [H1 H2].
    split; intros Hsat.
    + inversion Hsat as [| ? ? H3 H4]; subst.
      apply Forall_app in H4 as [H4 H5].
      apply Forall_app; split; try easy.
      apply Forall_app; split; try easy.
      apply H2. now econstructor.
    + apply Forall_app in Hsat as [[H3 H4]%Forall_app H5].
      specialize (H1 H3).
      inversion H1 as [| ? ? H6 H7]; subst.
      econstructor; try easy.
      apply Forall_app; split; try easy.
Qed.

Lemma matching_step_done:
  forall st sol,
    matching_step st = Success sol ->
    equations st = [].
Proof.
  intros [equs sol] sol' Heq. simpl.
  destruct equs as [| [dat pat] equs ]; try easy.
  unfold matching_step in Heq; simpl in *.
  destruct dat, pat;
  try destruct get;
  try destruct datum_eqb;
  try destruct String.eqb;
  try destruct decompose;
  try easy.
Qed.

Lemma matching_step_sol:
  forall st sol,
    matching_step st = Success sol ->
    sol = solution st.
Proof.
  intros [equs sol] sol' Heq. simpl.
  destruct equs as [| [dat pat] equs ]; try easy.
  unfold matching_step in Heq; simpl in *.
  - now inversion Heq.
  - apply matching_step_done in Heq.
    now inversion Heq.
Qed.

Lemma decompose_fail:
  forall l1 l2, decompose l1 l2 = None -> length l1 <> length l2.
Proof.
  induction l1 as [| x xs IH]; intros.
  - now destruct l2.
  - destruct l2; try easy. simpl in H.
    destruct (decompose xs l2) eqn:Heq; try easy.
    specialize (IH _ Heq).
    intros [=]. now rewrite H1 in IH.
Qed.

Lemma match_list_length:
  forall sub s1 l1 s2 l2 ,
    Matching sub (Dcmp s1 l1) (Pcmp s2 l2) ->
    length l1 = length l2.
Proof.
  intros. inversion H; subst.
  apply map_length.
Qed.

Lemma matching_step_failure:
  forall st,
    matching_step st = Failure ->
    forall sub, ~satisfy sub (state_as_equations st).
Proof.
  intros [equs sol] Heq sub Hcontr.
  destruct equs as [| [dat pat] equs]; try easy.
  unfold state_as_equations in Hcontr. simpl in *.
  inversion Hcontr as [| ? ? H1 H2]; subst.
  apply Forall_app in H2 as [H2 H3].
  destruct dat, pat.
  + unfold matching_step in Heq. simpl in *.
    destruct get eqn:Heq1; try easy.
    destruct datum_eqb eqn:Heq2; try easy.
    apply get_in, in_map_in_equations in Heq1.
    rewrite Forall_forall in H3.
    specialize (H3 _ Heq1). simpl in H3.
    unfold Matching in *; subst. simpl in *.
    apply datum_eqb_neq in Heq2.
    now rewrite H1 in Heq2.
  + unfold matching_step in Heq. simpl in *.
    destruct String.eqb eqn:Heq2.
    destruct decompose eqn:Heq3; try easy.
    apply decompose_fail in Heq3.
    apply match_list_length in H1.
    now rewrite H1 in Heq3.
    apply String.eqb_neq in Heq2.
    now inversion H1.
Qed.

(** ** Termination of the algorithm *)

(** Size of an equation *)
Definition equation_size '((x , y) : datum * pattern) : nat :=
  datum_size x + pattern_size y.

(** Size of a list of equations *)
Definition equations_size eqs : nat :=
  sum equation_size eqs.

(** Size of a state *)
Definition state_size (st : state) :=
  equations_size (equations st).

(** Ordering on states *)
Definition state_lt (st1 st2 : state) :=
  state_size st1 < state_size st2.

(** The ordering on states is well founded *)
Lemma state_lt_wf:
  well_founded state_lt.
Proof.
  apply (well_founded_ltof _ state_size).
Defined.

(** [matching_step] is strictly decreasing wrt [state_lt] *)
Lemma matching_step_mono:
  forall st1 st2,
    matching_step st1 = Update st2 ->
    state_lt st2 st1.
Proof.
  intros. red.
  destruct st1 as [equs sols]. simpl.
  destruct equs as [|[ [f1 l1] [| f2 l2]] equs]; unfold matching_step in H; simpl in *|-; try easy.
  + unfold state_size, equations_size, sum.
    destruct get eqn:Hget; try easy.
    destruct datum_eqb eqn:Heq; try easy.
    apply datum_eqb_eq in Heq; subst.
    all: inversion_clear H; simpl.
    all: apply sum_aux_mono; lia.
  + unfold state_size, equations_size.
    destruct String.eqb eqn:Heq1; try easy.
    destruct decompose as [equs'|] eqn:Heq2; try easy.
    inversion_clear H; simpl equations.
    fold (app [(Dcmp f1 l1, Pcmp f2 l2)] equs).
    do 2 rewrite sum_app.
    apply Nat.add_lt_mono_r.
    induction l1 as [| d1 l1 IH] in l2, equs', Heq2 |-* ; simpl in Heq2.
    - destruct l2 as [| d2 l2 ]; inversion_clear Heq2; cbn; lia.
    - destruct l2 as [| d2 l2 ]; [inversion Heq2|].
      destruct (decompose l1 l2) as [l|] eqn:Hdec; try easy.
      simpl in Heq2. inversion_clear Heq2.
      specialize (IH _ _ Hdec).
      repeat rewrite sum_cons in *.
      simpl equation_size in *.
      repeat rewrite sum_cons in *.
      lia.
Qed.

(** If there are no infinite decreasing sequences from a state [st1]
    and if [matchin_step st1 = Update st2] then
    then there are no inifinitely decreasing sequences starting from [st2]
*)
Lemma matching_iter_acc:
  forall st1 st2, Acc state_lt st1 -> matching_step st1 = Update st2 -> Acc state_lt st2.
Proof.
  intros * H1 H2.
  eapply Acc_inv; eauto.
  now apply matching_step_mono.
Defined.

(** An proof carrying datatype to classify elements of type [status] *)
Inductive status_cases (s : status) : Type :=
  | is_update   : sigT (fun st => s = Update st) -> status_cases s
  | is_success  : sigT (fun sol => s = Success sol) -> status_cases s
  | is_failure  : s = Failure -> status_cases s.

(** Any element of type [status] can be classified *)
Theorem status_dec:
  forall s : status, status_cases s.
Proof.
  intros [ | | ].
  + now apply is_failure.
  + apply is_update. eauto.
  + apply is_success. eauto.
Qed.

(** Iterating [matching_step] untill termination starting from an
    accessible state
    (i.e. a state from which there are no inifinite decreasing chains).
    
    The recursion is structural on the proof that the current
    state is accessible.
*)
Fixpoint matching_iter (st : state) (acc : Acc state_lt st) {struct acc} :=
  let s := matching_step st in
  match status_dec s with
  | is_success _ Hsol => Some (projT1 Hsol)
  | is_update _  Hupd => matching_iter (projT1 Hupd) (matching_iter_acc st (projT1 Hupd) acc (projT2 Hupd))
  | is_failure _ _    => None
  end.

(** The matching algorithm iterates the function [matching_step]
    starting with the initial equation to be solved.
*)
Definition matching (d : datum) (p : pattern) :=
  let st0 := Build_state [(d, p)] [] in
  matching_iter st0 (state_lt_wf st0).

(** ** Correctness of the Algorithm *)

(** *** Certificates *)

(** A first option is to have a partial algorithm that explicitely
    double checks that the computed solution to the matching problem
    is indeed a solution. This approach is sound but not complete.
*)
Definition certified_matching (dat : datum) (pat : pattern) : bool :=
  match matching dat pat with
  | Some sub => csubst pat (interp sub) =? dat
  | None => false
  end.

Lemma certified_matching_correct:
  forall dat pat, certified_matching dat pat = true -> Match dat pat.
Proof.
  intros. unfold certified_matching in H.
  destruct (matching dat pat) eqn:Heq; try easy.
  apply datum_eqb_eq in H.
  eexists. red. now rewrite H.
Qed.

(** *** Soundness and Completeness *)

(** What it means that the domain of a finite map covers the variables of
    of a given pattern
*)
Definition covers_pattern (sub : @fin_map datum) pat :=
  forall x, free_var pat x -> get sub x <> None.

(** What it means that the domain of a finite map covers the variables of
    of a set of equations
*)
Definition covers_equs (sub : @fin_map datum) (equs : list (datum * pattern)) :=
  Forall (fun '(_, pat) => covers_pattern sub pat) equs.

(** If a finite map covers the variables of a pattern, it also covers all its subpaterns *)
Lemma covers_subpattern:
  forall sub s x xs,
    covers_pattern sub (Pcmp s (x::xs)) ->
    covers_pattern sub x /\ covers_pattern sub (Pcmp s xs).
Proof.
  intros * H. split.
  - intros n Hn. apply H.
    now repeat econstructor.
  - intros n Hn. apply H.
    inversion Hn; subst.
    econstructor. now apply Exists_cons_tl.
Qed.

(** Extending a finite map that covers a pattern [pat]
    with a fresh binding does not change the result of
    applying the substitution to [pat]
*)
Lemma csubst_extend_map:
  forall pat sub x vx,
    get sub x = None ->
    covers_pattern sub pat ->
    csubst pat (interp sub) = csubst pat (interp ((x, vx)::sub)).
Proof.
  refine (pattern_induction _ _ _); try easy.
  - intros. unfold interp. simpl.
    destruct (x0 =? x)%nat eqn:Heq1.
    + apply Nat.eqb_eq in Heq1; subst.
      destruct get eqn:Heq2; try easy.
      specialize (H0 x (free_var_var x)).
      now rewrite Heq2 in H0.
    + destruct get eqn:Heq2; try easy.
  - intros * H1 * H2 H3. simpl.
    assert (Heq : map (fun p : pattern => csubst p (interp sub)) dats = map (fun p : pattern => csubst p (interp ((x, vx) :: sub))) dats).
    { apply map_ext_in. intros.
      rewrite Forall_forall in H1. apply H1; try easy.
      red. intros. apply H3. econstructor.
      apply Exists_exists. now exists a.
    }
    now rewrite Heq.
Qed.

(** Extending a finite map that covers equations [equs]
    with a fresh binding preserves the satisfiablity of [equs].
*)
Lemma satisfy_extend_map:
  forall sub x vx equs,
    get sub x = None ->
    covers_equs sub equs ->
    satisfy (interp sub) equs ->
    satisfy (interp ((x, vx)::sub)) equs.
Proof.
  intros * H1 H2 H3. induction equs as [|[dat pat] equs IH].
  - econstructor.
  - inversion H3; subst. clear H3.
    inversion H2; subst. clear H2.
    apply Forall_cons.
    + destruct pat; try easy.
      * unfold Matching, interp in H4 |-*. simpl in *.
        destruct (x =? n)%nat eqn:Heq2; try easy.
        apply Nat.eqb_eq in Heq2; subst.
        destruct (get sub n) eqn:Heq1; try easy.
        specialize (H3 n (free_var_var n)).
        now rewrite Heq1 in H3.
      * unfold Matching in H4 |-*.
        rewrite H4. clear H4.
        simpl. induction l; try easy.
        apply covers_subpattern in H3 as [H3 H4]. specialize (IHl H4).
        specialize (IH H6 H5).
        simpl. inversion IHl; subst.
        rewrite <- csubst_extend_map; auto.
    + apply (IH H6 H5).
Qed.

(** A valid substitution is a finite map
    with only one binding for each variable
*)
Inductive valid_subst : @fin_map datum -> Prop :=
  | valid_nil : valid_subst []
  | valid_cons x vx m :
    valid_subst m ->
    get m x = None ->
    valid_subst ((x, vx)::m).

(** A finite map covers itself *)
Lemma covers_itself:
  forall sub, covers_equs sub (map_as_equations sub).
Proof.
  induction sub as [| [x vx] sub IH].
  - econstructor.
  - unfold map_as_equations. simpl.
    apply Forall_forall.
    intros [dat pat] H; inversion_clear H as [[=H1 H2]|]; subst.
    + intros y Hy. inversion Hy; subst.
      simpl. now rewrite Nat.eqb_refl.
    + intros y Hy. simpl.
      destruct (x =? y)%nat; try easy.
      destruct (get sub y) eqn:Heq; try easy.
      apply in_equations_in_map in H0 as [z [-> Hz]].
      inversion Hy; subst.
      now rewrite Heq in Hz.
Qed.

(** A finite map satisfies itself *)
Lemma satisfy_self:
  forall sub, valid_subst sub -> satisfy (interp sub) (map_as_equations sub).
Proof.
  induction sub as [| (x, vx) sub IH].
  - econstructor.
  - intros H. inversion H; subst.
    specialize (IH H2).
    simpl. econstructor.
    + red. unfold interp. simpl.
      now rewrite Nat.eqb_refl.
    + apply satisfy_extend_map; auto.
      apply covers_itself.
Qed.

(** Taking a step of the matching algorithm preserves the well-formedness of the solution *)
Theorem matching_step_valid_subst:
  forall st1 st2,
    valid_subst (solution st1) ->
    matching_step st1 = Update st2 ->
    valid_subst (solution st2).
Proof.
  intros [[| [dat pat] equs1] sol1] [equs2 sol2] H1 H2; simpl solution in *; try easy.
  cbn in H2.
  destruct dat, pat; try easy.
  - destruct get eqn:Heq1.
    destruct datum_eqb eqn:Heq2; try easy.
    + apply datum_eqb_eq in Heq2; subst.
      inversion H2; subst; auto.
    + inversion H2; subst. clear H2.
      now econstructor.
  - destruct String.eqb eqn:Heq1; try easy.
    apply String.eqb_eq in Heq1; subst.
    destruct decompose eqn:Heq2; try easy.
    now inversion H2; subst.
Qed.

(** Taking several steps of the matching algorithm preserves the well-formedness of the solution *)
Lemma matching_iter_valid_subst:
  forall st sub Hacc, valid_subst (solution st) -> matching_iter st Hacc = Some sub -> valid_subst sub.
Proof.
  induction st using (well_founded_induction state_lt_wf). intros * Hvalid.
  destruct Hacc as [Hacc]; cbn.
  destruct status_dec as [[st' Hst'] | [sol Hsol] |]; try easy; simpl.
  - intros Heq.
    pose proof (Hlt := matching_step_mono _ _ Hst').
    pose proof (Hsub := matching_step_valid_subst _ _ Hvalid Hst').
    eapply H; eauto.
  - apply matching_step_sol in Hsol; subst.
    now intros [=<-].
Qed.

(** Taking several steps of the matching algorithm starting in a well formed state [st]
    generates a solution to the equations described by [st]
*)
Lemma matching_iter_sound:
  forall st sub Hacc, valid_subst (solution st) -> matching_iter st Hacc = Some sub -> satisfy (interp sub) (state_as_equations st).
Proof.
  induction st using (well_founded_induction state_lt_wf). intros *.
  destruct Hacc as [Hacc]; cbn. intros Hvalid.
  destruct status_dec as [[st' Hst'] | [sol Hsol] |]; try easy; simpl.
  - pose proof (Hlt := matching_step_mono _ _ Hst').
    pose proof (Heq := matching_step_equiv _ _ Hst' (interp sub)).
    pose proof (Hvalid' := matching_step_valid_subst _ _ Hvalid Hst').
    rewrite Heq. now apply H.
  - pose proof (Hsol' := matching_step_sol _ _ Hsol).
    pose proof (Hequs := matching_step_done _ _ Hsol).
    destruct st as [equs sols]. unfold state_as_equations.
    simpl in *; subst. simpl.
    intros [=<-]. cbn in Hsol. inversion_clear Hsol.
    now apply satisfy_self.
Qed.

(** If the set of equations generated by a state [st] has a solution,
   then iterating [matching_step] starting from [st] eventually gives a solution
*)
Lemma matching_iter_complete:
  forall st sub Hacc, satisfy sub (state_as_equations st) -> exists sub, matching_iter st Hacc = Some sub.
Proof.
  induction st using (well_founded_induction state_lt_wf). intros * Hsat.
  destruct Hacc as [Hacc]; cbn.
  destruct status_dec as [[st' Hst'] | [sol Hsol] |]; simpl.
  - pose proof (Hlt := matching_step_mono _ _ Hst').
    pose proof (Heq := matching_step_equiv _ _ Hst' sub).
    rewrite Heq in Hsat. 
    specialize (H _ Hlt sub (Hacc _ (matching_step_mono st st' Hst')) Hsat) as [sub' Hsub'].
    eexists. apply Hsub'.
  - now eexists sol.
  - eapply matching_step_failure in e.
    now apply e in Hsat.
Qed.

(** [matching] is a sound algorithm to solve matching problems *)
Lemma matching_sound:
  forall dat pat sub, matching dat pat = Some sub -> Matching (interp sub) dat pat.
Proof.
  intros.
  unfold matching in H.
  apply matching_iter_sound in H.
  - now inversion H.
  - econstructor.
Qed.

(** [matching] is a complete algorithm to solve matching problems *)
Lemma matching_complete:
  forall dat pat, Match dat pat -> exists sub, matching dat pat = Some sub.
Proof.
  intros * [sub Hsub].
  unfold matching.
  apply (matching_iter_complete _ sub).
  unfold state_as_equations. simpl.
  now econstructor.
Qed.