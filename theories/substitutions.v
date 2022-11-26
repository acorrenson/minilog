From Coq Require Import List String Arith.
From minilog Require Import utils data.
Import ListNotations.

(** * Substitutions and Unifiers *)

(** Closed substitutions (functions from variables to [datum]) *)
Definition csubstitution := nat -> datum.

(** Open substitutions (functions from variables to [pattern]) *)
Definition psubstitution := nat -> pattern.

(** Apply a closed substitution to a pattern *)
Fixpoint csubst (p : pattern) (sub : csubstitution) : datum :=
  match p with
  | Papp f pats =>
    Dapp f (map (fun p => csubst p sub) pats)
  | Pvar n => sub n
  end.

(** Apply an open substitution to a pattern *)
Fixpoint psubst (p : pattern) (sub : psubstitution) : pattern :=
  match p with
  | Papp f pats =>
    Papp f (map (fun p => psubst p sub) pats)
  | Pvar n => sub n
  end.

Definition dom (sub : psubstitution) : nat -> Prop :=
  fun x => sub x <> Pvar x.

Definition codom (sub : psubstitution) : nat -> Prop :=
  fun x => exists y, free_var (sub y) x.

Definition fin_csubst := (fin_map datum).
Definition fin_psubst := (fin_map pattern).

(** Intepreting a finite map as a csubstitution *)
Definition cinterp (sub : fin_csubst) : csubstitution :=
  fun x => match get sub x with None => Dcst "" | Some vx => vx end.

(** Intepreting a finite map as a psubstitution *)
Definition pinterp (sub : fin_psubst) : psubstitution :=
  fun x => match get sub x with None => Pvar x | Some vx => vx end.

Coercion cinterp : fin_csubst >-> csubstitution.
Coercion pinterp : fin_psubst >-> psubstitution.

Definition replace (p : pattern) (x : nat) (q : pattern) :=
  psubst p (pinterp [(x, q)]).

Notation "p '.[' x ':=' q ']'" := (replace p x q) (at level 60).
Notation "p '.[' s ']'" := (psubst p s) (at level 60).

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

Theorem free_subst_1:
  forall pat x vx,
    ~free_var vx x ->
    ~free_var (pat .[ x := vx]) x.
Proof.
  refine (pattern_induction _ _ _).
  - intros y x vx Hfree Hcontr.
    unfold replace, pinterp in Hcontr. simpl in Hcontr.
    destruct (x =? y)%nat eqn:Heq; try easy.
    apply Nat.eqb_neq in Heq. now inversion Hcontr; subst.
  - intros f dats IH x vx Hfree Hcontr.
    inversion Hcontr as [|? ? ? H]; subst. clear Hcontr.
    apply Exists_exists in H as [pat' [Hpat1 Hpat2]].
    apply map_in in Hpat1 as [pat [Hpat1 ->]].
    rewrite Forall_forall in IH.
    now specialize (IH _ Hpat1 _ _ Hfree).
Qed.

Theorem free_subst_2:
  forall pat x y vy,
    ~free_var vy y ->
    ~free_var pat y ->
    ~free_var (pat .[ x := vy]) y.
Proof.
  refine (pattern_induction _ _ _).
  - intros x y z vz Hfree1 Hfree2 Hcontr.
    unfold replace, pinterp in Hcontr. simpl in Hcontr.
    destruct (y =? x)%nat eqn:Heq; try easy.
  - intros f dats IH x y vy Hfree1 Hfree2 Hcontr.
    inversion Hcontr as [|? ? ? H]; subst. clear Hcontr.
    apply Exists_exists in H as [pat' [Hpat1 Hpat2]].
    apply map_in in Hpat1 as [pat [Hpat1 ->]].
    rewrite Forall_forall in IH.
    assert (~free_var pat y).
    { intros Hcontr. apply Hfree2.
      econstructor. apply Exists_exists.
      now exists pat.
    }
    apply (IH _ Hpat1 _ _ _ Hfree1 H Hpat2).
Qed.

(** ** Operations on substitutions *)

Declare Scope subst.
Delimit Scope subst with subst.

(** Composing two subtitutions ([s2] after [s1]) *)
Definition compose (s2 s1 : psubstitution) (n : nat) : pattern :=
  psubst (s1 n) s2.

Infix "•" := compose (at level 80) : subst.

Definition equ (s1 s2 : psubstitution) :=
  forall n, s1 n = s2 n.

Infix "≡" := equ (at level 90) : subst.

Definition subst_le (s1 s2 : psubstitution) : Prop :=
  exists s3, (s3 • s1 ≡ s2)%subst.

Infix "<=" := subst_le (at level 70).

(** ** Matching *)

(** What is means that a substitution is a matching for a [datum] and a [pattern] *)
Definition Matching sub (dat : datum) (pat : pattern) : Prop :=
  dat = csubst pat sub.

(** What is means that a [pattern] matches a [datum] *)
Definition Match (dat : datum) (pat : pattern) : Prop :=
  exists sub, Matching sub dat pat.

(** ** Unifiers *)

(** What is means that to be a unifier *)
Definition Unifier (sub : psubstitution) (pat1 pat2 : pattern) : Prop :=
  psubst pat1 sub = psubst pat2 sub.

Definition Mgu (sub : psubstitution) (pat1 pat2 : pattern) : Prop :=
  Unifier sub pat1 pat2 /\ forall sub', Unifier sub' pat1 pat2 -> (sub <= sub')%subst.

(** What is means that two patterns are unifiable *)
Definition Unifiable (pat1 pat2 : pattern) : Prop :=
  exists sub, Unifier sub pat1 pat2.

Lemma psubst_compose :
  forall s1 s2 t, psubst t (s2 • s1)%subst = psubst (psubst t s1) s2.
Proof.
  intros s1 s2. apply pattern_induction; simpl; try easy.
  intros f ts Hts. induction ts; simpl; auto.
  f_equal. inversion Hts; subst. rewrite H1.
  specialize (IHts H2). clear H2.
  simpl in IHts. now injection IHts as ->.
Qed.