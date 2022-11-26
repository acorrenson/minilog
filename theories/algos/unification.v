From Coq Require Import String List Arith Lia.
From minilog Require Import data utils substitutions.
Import ListNotations.

(** * Verified Unification Algorithm *)

(** ** Finite substitutions and replacements *)

Definition replace (p : pattern) (x : nat) (q : pattern) :=
  psubst p (pinterp [(x, q)]).

Notation "p '.[' x ':=' q ']'" := (replace p x q) (at level 60).
Notation "p '.[' s ']'" := (psubst p s) (at level 60).

(** Replacement in a list of equations of the forme [term = term] *)
Definition replace_all_1 (l : list (pattern * pattern)) (x : nat) (p : pattern) :=
  map (fun '(p1, p2) => (p1.[x := p], p2.[x := p])) l.

(** Replacement in a list of equations of the form [var = term].
    Only the right hand sides are modified.
*)
Definition replace_all_2 (l : list (nat * pattern)) (x : nat) (p : pattern) :=
  map (fun '(y, py) => (y, py.[x := p])) l.

(** ** Unifiers *)

(** What it means that a substitution unifies 2 patterns *)
Definition unifier u p1 p2 : Prop :=
  p1.[u] = p2.[u].

(** What it means to be a solution to a set of equations *)
Definition satisfy (u : psubstitution) equs :=
  Forall (fun '(x, y) => unifier u x y) equs.

Lemma unifier_cons:
  forall u f1 pat1 pats1 f2 pat2 pats2,
    unifier u (Papp f1 (pat1::pats1)) (Papp f2 (pat2::pats2)) <->
    (unifier u pat1 pat2 /\ unifier u (Papp f1 pats1) (Papp f2 pats2)).
Proof.
  intros. split.
  - intros H. inversion H; subst.
    unfold unifier. split; simpl; auto.
    now rewrite H3.
  - intros [H1 H2].
    unfold unifier in *. simpl.
    rewrite H1. now injection H2 as -> ->.
Qed.

(** ** Algorithm *)

(** As for matching, a state of the algorithm is a list of equations to be solved and a current solution.
    The only difference is that unification equations are of the form [(pattern, pattern)]
    Solutions are represented as finite maps from variables to patterns ([pattern])
*)
Record state := {
  equations : list (pattern * pattern);
  solution  : @fin_map pattern;
}.

(** At every iteration, the algorithm either fails, update the current state,
    or terminates with a solution *)
Inductive status :=
  | Failure
  | Update (st : state)
  | Success (sub : @fin_map pattern).

(** What it means for to set of equations to be equivalent *)
Definition equiv (equs1 equs2 : list (pattern * pattern)) :=
  forall u, satisfy u equs1 <-> satisfy u equs2.

(** Intepreting a finite map as a set of equations *)
Definition map_as_equations (m : @fin_map pattern) :=
  map (fun '(x, y) => (Pvar x, y)) m.

(** Intepreting a state as set of equations *)
Definition state_as_equations (st : state) :=
  equations st ++ map_as_equations (solution st).

Definition state_equiv (st1 st2 : state) :=
  equiv (state_as_equations st1) (state_as_equations st2).

(** Decompose the problem of unifying two vectors
    into a list of equations.
    The generated equations are collected on top
    of a provided accumulator.
*)
Fixpoint decompose (l1 : list pattern) (l2 : list pattern) :=
  match l1, l2 with
  | [], [] => Some []
  | x::xs, y::ys =>
    do equs <- decompose xs ys;
    Some ((x, y)::equs)
  | _, _ => None
  end.

Definition unification_step (st : state) :=
  match equations st with
  | [] => Success (solution st)
  | (t1, t2)::xs =>
    match t1, t2 with
    | Papp f1 l1, Papp f2 l2 =>
      if (f1 =? f2)%string then
        match decompose l1 l2 with
        | Some equs => Update (Build_state (equs ++ xs) (solution st))
        | None => Failure
        end
      else Failure
    | Pvar n, t | t, Pvar n =>
      if is_free t n then
        Failure
      else
        Update (Build_state (replace_all_1 xs n t) ((n, t)::(replace_all_2 (solution st) n t)))
    end
  end.

Lemma decompose_equiv:
  forall s1 s2 l1 l2 l,
    (s1 =? s2)%string = true ->
    decompose l1 l2 = Some l ->
    equiv l [(Papp s1 l1, Papp s2 l2)].
Proof.
  intros * ->%String.eqb_eq Hdec sub.
  induction l2 in l, l1, Hdec, sub |-*.
  - destruct l1; try easy.
    inversion_clear Hdec.
    repeat econstructor.
  - destruct l1; simpl in *; try easy.
    destruct (decompose l1 l2) as [l'|] eqn:Heq; simpl in *; try easy.
    inversion Hdec; subst. clear Hdec.
    specialize (IHl2 _ _ Heq sub) as [H1 H2].
    split; intros.
    + inversion_clear H as [| ? ? H3 H4].
      specialize (H1 H4).
      inversion_clear H1 as [| ? ? H5 _].
      repeat econstructor.
      apply unifier_cons.
      now repeat econstructor.
    + inversion H as [| ? ? H3 _]; subst.
      apply unifier_cons in H3 as [H3 H4].
      econstructor; auto.
      apply H2. now repeat econstructor.
Qed.

Lemma subst_replace_var:
  forall x y sub pat,
    sub x = sub y ->
    pat.[sub] = pat.[x := Pvar y].[sub].
Proof.
  intros x y sub.
  refine (pattern_induction _ _ _).
  - intros z Heq1. unfold replace, pinterp. simpl.
    destruct (x =? z)%nat eqn:Heq2; auto.
    now apply Nat.eqb_eq in Heq2; subst.
  - intros f dats Hdats Heq1. simpl. f_equal.
    induction Hdats; auto.
    specialize (H Heq1). simpl. now f_equal.
Qed.

Lemma subst_replace:
  forall x px sub pat,
    sub x = px.[sub] ->
    pat.[sub] = pat.[x := px].[sub].
Proof.
  intros x px sub.
  refine (pattern_induction _ _ _).
  - intros y Heq1.
    unfold replace, pinterp. simpl.
    destruct (x =? y)%nat eqn:Heq2; auto.
    now apply Nat.eqb_eq in Heq2; subst.
  - intros f dats H1 H2.
    simpl. f_equal.
    rewrite map_map.
    apply map_ext_in.
    intros p Hp.
    rewrite Forall_forall in H1.
    now specialize (H1 _ Hp H2).
Qed.

Lemma replace_all_1_equiv':
  forall equs sub x px,
    sub x = px.[sub] ->
    satisfy sub equs <->
    satisfy sub (replace_all_1 equs x px).
Proof.
  intros.
  induction equs as [| [pat1 pat2] equs IH]; try easy.
  split; intros Hsat.
  - inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    econstructor; auto. red.
    now do 2 rewrite <- subst_replace by auto.
  - inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    red in H1. do 2 rewrite <- subst_replace in H1 by auto.
    now econstructor.
Qed.

Lemma replace_all_1_equiv:
  forall equs sub x y,
    sub x = sub y ->
    satisfy sub equs <->
    satisfy sub (replace_all_1 equs x (Pvar y)).
Proof.
  intros * H.
  induction equs as [| [pat1 pat2] equs IH]; try easy.
  split; intros Hsat.
  + inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    econstructor; auto. red.
    now do 2 rewrite <- subst_replace_var by auto.
  + inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    red in H1. do 2 rewrite <- subst_replace_var in H1 by auto.
    now econstructor.
Qed.

Lemma replace_all_2_equiv':
  forall equs sub x px,
    sub x = px.[sub] ->
    satisfy sub (map_as_equations equs) <->
    satisfy sub (map_as_equations (replace_all_2 equs x px)).
Proof.
  intros.
  induction equs as [| [y py] equs IH]; try easy.
  split; intros Hsat.
  - inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    econstructor; auto. red.
    now rewrite <- subst_replace.
  - inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    red in H1. rewrite <- subst_replace in H1 by auto.
    now econstructor.
Qed.

Lemma replace_all_2_equiv:
  forall equs sub x y,
    sub x = sub y ->
    satisfy sub (map_as_equations equs) <->
    satisfy sub (map_as_equations (replace_all_2 equs x (Pvar y))).
Proof.
  intros * H.
  induction equs as [| [z patz] equs IH]; try easy.
  split; intros Hsat.
  + inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    econstructor; auto. red.
    now rewrite H1, <- subst_replace_var by auto.
  + inversion Hsat as [| ? ? H1 H2]; subst.
    apply IH in H2.
    red in H1. rewrite <- subst_replace_var in H1 by auto.
    now econstructor.
Qed.

Lemma unify_replace:
  forall sub x patx pat1 pat2,
    unifier sub (Pvar x) patx ->
    unifier sub pat1 pat2 <->
    unifier sub (pat1.[x := patx]) (pat2.[x := patx]).
Proof.
  intros. split; intros.
  - red. now do 2 rewrite <- subst_replace by auto.
  - red in H0. now do 2 rewrite <- subst_replace in H0 by auto.
Qed.

Lemma map_in:
  forall A B (f : A -> B) (l : list A) b,
    In b (List.map f l) -> exists a, In a l /\ b = f a.
Proof.
  intros. induction l; try easy.
  destruct H as [<- | H].
  - repeat econstructor.
  - specialize (IHl H) as (a' & Ha' & ->).
    exists a'. split; auto. now right.
Qed.

Theorem unification_step_equiv:
  forall st1 st2,
    unification_step st1 = Update st2 ->
    state_equiv st1 st2.
Proof.
  intros [equs1 sol1] [equs2 sol2] Hstep sub.
  induction equs1 as [| [dat1 pat1] equs1 _] in equs2, sol2, Hstep |-*; try easy.
  destruct dat1, pat1; cbn in Hstep.
  - destruct (n0 =? n)%nat eqn:Heq1; try easy.
    inversion Hstep; subst. clear Hstep.
    apply Nat.eqb_neq in Heq1.
    unfold state_as_equations. simpl.
    split.
    + intros H. inversion H as [| ? ? H1 H2]; subst.
      apply Forall_app in H2 as [H2 H3].
      apply Forall_app. repeat econstructor; auto.
      now apply replace_all_1_equiv.
      now apply replace_all_2_equiv.
    + intros [H1 H2]%Forall_app.
      inversion H2 as [| ? ? H3 H4]; subst.
      econstructor; auto.
      apply replace_all_1_equiv in H1; auto.
      apply replace_all_2_equiv in H4; auto.
      now apply Forall_app; split.
  - destruct (existsb)%nat eqn:Heq1; try easy.
    inversion Hstep; subst. clear Hstep.
    unfold state_as_equations. simpl.
    split.
    + simpl. intros H. inversion H as [| ? ? H1 H2]; subst.
      apply Forall_app in H2 as [H2 H3]. clear H.
      apply Forall_app. repeat econstructor; auto.
      now apply replace_all_1_equiv'.
      now apply replace_all_2_equiv'.
    + intros [H1 H2]%Forall_app. inversion H2 as [| ? ? H3 H4]; subst. clear H2.
      econstructor; auto.
      apply Forall_app. split.
      pose proof (replace_all_1_equiv' equs1 _ _ _ H3).
      now apply H in H1.
      fold (replace_all_2 sol1 n (Papp s l)) in H4.
      now apply replace_all_2_equiv' in H4.
  - destruct (existsb)%nat eqn:Heq1; try easy.
    inversion Hstep; subst. clear Hstep.
    unfold state_as_equations. simpl.
    fold (replace_all_2 sol1 n (Papp s l)).
    split.
    + simpl. intros H. inversion H as [| ? ? H1 H2]; subst.
      red in H1. symmetry in H1. clear H.
      apply Forall_app in H2 as [H2 H3].
      apply Forall_app. repeat econstructor; auto.
      now apply replace_all_1_equiv'.
      now apply replace_all_2_equiv'.
    + simpl. intros [H1 H2]%Forall_app.
      inversion H2 as [| ? ? H3 H4]; subst. clear H2.
      red in H3. symmetry in H3.
      econstructor; auto.
      apply Forall_app. split.
      now apply replace_all_1_equiv' in H1.
      now apply replace_all_2_equiv' in H4.
  - destruct (s =? s0)%string eqn:Heq1; try easy.
    destruct (decompose l l0) eqn:Heq2; try easy.
    apply String.eqb_eq in Heq1; subst.
    inversion Hstep; subst. clear Hstep.
    apply (decompose_equiv s0 s0 _ _ _ (String.eqb_refl s0)) in Heq2.
    specialize (Heq2 sub).
    unfold state_as_equations. simpl. split.
    + intros H. inversion H as [|? ? H2 H3]; subst.
      clear H. apply Forall_app in H3 as [H3 H4].
      do 2 (apply Forall_app; split; auto).
      apply Heq2. now econstructor.
    + intros [[H1 H2]%Forall_app H3]%Forall_app.
      apply Forall_cons.
      apply Heq2 in H1. now inversion H1.
      apply Forall_app; split; auto.
Qed.

(** ** INVARIAAAAAANT !!!! *)

(** For all binding [x = vx] in the current solution,
    [x] does not occur in [vx] and in the remaning
    equations.
*)
Definition invariant (st : state) :=
  forall x vx, In (x, vx) (solution st) ->
    ~(free_var vx x) /\
    forall pat1 pat2, In (pat1, pat2) (equations st) ->
      ~free_var pat1 x /\ ~free_var pat2 x.

Lemma unification_step_invariant:
  forall st1 st2,
    invariant st1 ->
    unification_step st1 = Update st2 ->
    invariant st2.
Proof.
  intros [equs1 sol1] [equs2 sol2] H1 H2.
  unfold unification_step in H2. simpl in *.
  destruct equs1 as [| [pat1 pat2] equs1 ]; try easy.
  destruct pat1.
  - destruct is_free eqn:Heq1; try easy.
    injection H2 as <- <-.
    intros x vx. simpl.
    intros [[=->->] | Hin].
    + split. now apply is_free_false.
      intros pat1 pat2 Hin.
      apply map_in in Hin as [[pat1' pat2'] [Hin [=->->]]].
      admit. (* should be trivial (no matter the context) *)
    + apply map_in in Hin as [[y vy] [Hin [=->->]]].
      specialize (H1 _ _ Hin) as [H1 H2]. simpl in H2.
      specialize (H2 _ _ (or_introl eq_refl)) as [H2 H3].
      admit. (* should be trivial in context *)
  - destruct pat2.
    + destruct is_free eqn:Heq1; try easy.
      injection H2 as <- <-.
      intros x vx. simpl.
      intros [[=<-<-] | Hin].
      * split. now apply is_free_false.
        intros pat1 pat2 Hin.
        apply map_in in Hin as [[pat1' pat2'] [Hin [=->->]]].
        admit. (* should be trivial (no matter the context) *)
      * apply map_in in Hin as [[y vy] [Hin [=->->]]].
        admit. (* should be trivial in context *)
    + destruct (s =? s0)%string eqn:Heq; try easy.
      apply String.eqb_eq in Heq as <-.
      destruct decompose eqn:Heq; try easy.
      injection H2 as <- <-.
        admit. (* need a lemma about variables after decomposition *)
Admitted.