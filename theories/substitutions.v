From Coq Require Import List String.
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