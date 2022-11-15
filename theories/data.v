From Coq Require Import String List Program.Wf.
From minilog Require Import utils.
Import ListNotations.

(** * An simple algebra of first order terms to describe databases *)

(** ** Syntax *)

(** A [datum] is function symbol applied to a set of [datum] *)
Inductive datum :=
  | Dcmp : string -> list datum -> datum.

Definition Dcst (c : string) := Dcmp c [].

(** Patterns over [datum] *)
Inductive pattern :=
  | Pvar : nat -> pattern
  | Pcmp : string -> list pattern -> pattern.

Definition Pcst (c : string) := Pcmp c [].

(** Free variables of a pattern *)
Inductive free_var : pattern -> nat -> Prop :=
  | free_var_var x : free_var (Pvar x) x
  | free_var_cmp x f l :
    Exists (fun p => free_var p x) l -> free_var (Pcmp f l) x.

Definition is_free (p : pattern) (x : nat) : bool :=
  true (* todo *).

Axiom is_free_iff:
  forall p x, is_free p x = true <-> free_var p x.

(** ** Induction Principles *)

(** We need a stronger induction principle that
    the one infered by Coq.
*)
Fixpoint datum_induction
  (P : datum -> Prop)
  (Hind : forall f dats, Forall P dats -> P (Dcmp f dats))
  (dat : datum) : P dat :=
  match dat with
  | Dcmp f dats =>
    let helper := fix F l :=
      match l as l' return Forall P l' with
      | nil => Forall_nil P
      | cons x xs =>
        @Forall_cons _ P x xs (datum_induction P Hind x) (F xs)
      end
    in
    Hind f dats (helper dats)
  end.

(** We need a stronger induction principle that
  the one infered by Coq.
*)
Fixpoint pattern_induction
  (P : pattern -> Prop)
  (H1 : forall x, P (Pvar x))
  (Hind : forall f dats, Forall P dats -> P (Pcmp f dats))
  (pat : pattern) : P pat :=
  match pat with
  | Pvar x => H1 x
  | Pcmp f pats =>
    let helper := fix F l :=
      match l as l' return Forall P l' with
      | nil => Forall_nil P
      | cons x xs =>
        @Forall_cons _ P x xs (pattern_induction P H1 Hind x) (F xs)
      end
    in
    Hind f pats (helper pats)
  end.

Declare Scope datum.
Delimit Scope datum with datum.
Declare Scope pattern.
Delimit Scope pattern with pattern.

Fixpoint datum_size (d : datum) : nat :=
  match d with
  | Dcmp _ dats =>
    1 + sum datum_size dats
  end.

Fixpoint pattern_size (p : pattern) : nat :=
  match p with
  | Pvar _ => 1
  | Pcmp _ pats =>
    1 + sum pattern_size pats
  end.

(** Boolean equality for [datum] *)
Fixpoint datum_eqb (d1 d2 : datum) : bool :=
  match d1, d2 with
  | Dcmp f1 l1, Dcmp f2 l2 =>
    let fix F l1 l2 :=
      match l1, l2 with
      | [], [] => true
      | x::xs, y::ys => andb (datum_eqb x y) (F xs ys)
      | _, _ => false
      end
    in andb (f1 =? f2)%string (F l1 l2)
  end.

Lemma datum_eqb_refl:
  forall x, datum_eqb x x = true.
Proof.
  refine (datum_induction _ _); intros; simpl.
  apply Bool.andb_true_iff; split.
  apply String.eqb_refl.
  induction dats; try easy.
  inversion H as [| ? ? H1 H2]; subst.
  rewrite H1. simpl.
  now apply IHdats.
Qed.

Lemma datum_eqb_eq:
  forall x y, datum_eqb x y = true <-> x = y.
Proof.
  refine (datum_induction _ _).
  intros f dats IH y. split; intros.
  + destruct y; simpl in H; try easy.
    apply Bool.andb_true_iff in H as [->%String.eqb_eq H].
    induction l in dats, H, IH, s |-*.
    destruct dats; try easy.
    destruct dats; try easy.
    apply Bool.andb_true_iff in H as [H1 H2].
    inversion_clear IH as [|? ? H3 H4].
    apply H3 in H1 as ->.
    assert (Dcmp s dats = Dcmp s l).
    apply IHl; auto.
    now inversion H.
  + destruct y; simpl in H; try easy.
    inversion_clear H.
    apply datum_eqb_refl.
Qed.

Lemma datum_eqb_neq:
  forall x y, datum_eqb x y = false -> x <> y.
Proof.
  intros * Hfalse Hcontr.
  apply datum_eqb_eq in Hcontr.
  now rewrite Hfalse in Hcontr.
Qed.

Infix "=?" := (datum_eqb)%datum.

(** ** First Order Substitution *)

(** Closed substitutions (functions from variables to [datum]) *)
Definition csubstitution := nat -> datum.

(** Open substitutions (functions from variables to [pattern]) *)
Definition psubstitution := nat -> pattern.

(** Apply a closed substitution to a pattern *)
Fixpoint csubst (p : pattern) (sub : csubstitution) : datum :=
  match p with
  | Pcmp f pats =>
    Dcmp f (map (fun p => csubst p sub) pats)
  | Pvar n => sub n
  end.

(** Apply an open substitution to a pattern *)
Fixpoint psubst (p : pattern) (sub : psubstitution) : pattern :=
  match p with
  | Pcmp f pats =>
    Pcmp f (map (fun p => psubst p sub) pats)
  | Pvar n => sub n
  end.

(** What is means that a substitution is a matching for a [datum] and a [pattern] *)
Definition Matching sub (dat : datum) (pat : pattern) : Prop :=
  dat = csubst pat sub.

(** What is means that a [pattern] matches a [datum] *)
Definition Match (dat : datum) (pat : pattern) : Prop :=
  exists sub, Matching sub dat pat.

(** What is means that two patterns are unifiable *)
Definition Unify (pat1 pat2 : pattern) : Prop :=
  exists sub, psubst pat1 sub = psubst pat2 sub.

(** Composing two subtitutions ([s2] after [s1]) *)
Definition compose (s2 s1 : psubstitution) (n : nat) : pattern :=
  psubst (s1 n) s2.

Infix "•" := compose (at level 80).

Definition equ (s1 s2 : psubstitution) :=
  forall n, s1 n = s2 n.

Infix "≡" := equ (at level 90).

Definition subst_le (s1 s2 : psubstitution) : Prop :=
  exists s3, s3 • s1 ≡ s2.

Infix "⪯" := subst_le (at level 90).

Lemma psubst_compose :
  forall s1 s2 t, psubst t (s2 • s1) = psubst (psubst t s1) s2.
Proof.
  intros s1 s2. apply pattern_induction; simpl; try easy.
  intros f ts Hts. induction ts; simpl; auto.
  f_equal. inversion Hts; subst. rewrite H1.
  specialize (IHts H2). clear H2.
  simpl in IHts. now injection IHts as ->.
Qed.