From Coq Require Import String List Arith Lia.
From minilog Require Import data utils.
Import ListNotations.

(** * Verified Unification Algorithm *)

(** ** Finite substitutions and replacements *)

Definition fin_subst := @fin_map pattern.

Definition interp (f : fin_subst ) : psubstitution :=
  fun x => match get f x with Some vx => vx | None => Pvar x end.

Definition replace (p : pattern) (x : nat) (q : pattern) :=
  psubst p (interp [(x, q)]).

Notation "p '⟨' x ':=' q '⟩'" := (replace p x q) (at level 60).
Notation "p '.⟨' s '⟩'" := (psubst p s) (at level 60).

(** Replacement in a list of equations of the forme [term = term] *)
Definition replace_all_1 (l : list (pattern * pattern)) (x : nat) (p : pattern) :=
  map (fun '(p1, p2) => (p1⟨x := p⟩, p2⟨x := p⟩)) l.

(** Replacement in a list of equations of the form [var = term].
    Only the right hand sides are modified.
*)
Definition replace_all_2 (l : list (nat * pattern)) (x : nat) (p : pattern) :=
  map (fun '(y, py) => (y, py⟨x := p⟩)) l.

(** ** Unifiers *)

(** What it means that a substitution unifies 2 patterns *)
Definition unifier u p1 p2 : Prop :=
  p1.⟨u⟩ = p2.⟨u⟩.

(** What it means to be a solution to a set of equations *)
Definition satisfy (u : psubstitution) equs :=
  Forall (fun '(x, y) => unifier u x y) equs.

Lemma unifier_cons:
  forall u f1 pat1 pats1 f2 pat2 pats2,
    unifier u (Pcmp f1 (pat1::pats1)) (Pcmp f2 (pat2::pats2)) <->
    (unifier u pat1 pat2 /\ unifier u (Pcmp f1 pats1) (Pcmp f2 pats2)).
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
    | Pcmp f1 l1, Pcmp f2 l2 =>
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
    equiv l [(Pcmp s1 l1, Pcmp s2 l2)].
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
    admit.
  - destruct (existsb)%nat eqn:Heq1; try easy.
    inversion Hstep; subst. clear Hstep.
    unfold state_as_equations. simpl.
    admit.
  - destruct (existsb)%nat eqn:Heq1; try easy.
    inversion Hstep; subst. clear Hstep.
    unfold state_as_equations. simpl.
    admit.
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
Admitted.

(** ** INVARIAAAAAANT !!!! *)

(** For all binding [x = vx] in the current solution,
    [x] is does not occur in [vx] and in the remaning
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
Admitted.