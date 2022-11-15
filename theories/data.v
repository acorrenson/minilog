From Coq Require Import String List Program.Wf.
From minilog Require Import utils.
Import ListNotations.

(** * An simple algebra of first order terms to describe databases *)

(** A [datum] is either a constant or a function symbol applied to a set of [datum] *)
Inductive datum :=
  | Dcst : string -> datum
  | Dcmp : string -> list datum -> datum.

(** Patterns over [datum] *)
Inductive pattern :=
  | Pvar : nat -> pattern
  | Pcst : string -> pattern
  | Pcmp : string -> list pattern -> pattern.

(** Free variables of a pattern *)
Inductive free_var : pattern -> nat -> Prop :=
  | free_var_var x : free_var (Pvar x) x
  | free_var_cmp x f l :
    Exists (fun p => free_var p x) l -> free_var (Pcmp f l) x.

(** Closed substitutions (functions from variables to [datum]) *)
Definition csubstitution := nat -> datum.

(** Open substitutions (functions from variables to [pattern]) *)
Definition psubstitution := nat -> pattern.

(** Apply a closed substitution to a pattern *)
Fixpoint csubst (p : pattern) (sub : csubstitution) : datum :=
  match p with
  | Pcst c => Dcst c
  | Pcmp f pats =>
    Dcmp f (map (fun p => csubst p sub) pats)
  | Pvar n => sub n
  end.

(** Apply an open substitution to a pattern *)
Fixpoint psubst (p : pattern) (sub : psubstitution) : pattern :=
  match p with
  | Pcst c => p
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

(** We need a stronger induction principle that
    the one infered by Coq.
*)
Fixpoint datum_induction
  (P : datum -> Prop)
  (H0 : forall c, P (Dcst c))
  (Hind : forall f dats, Forall P dats -> P (Dcmp f dats))
  (dat : datum) : P dat :=
  match dat with
  | Dcst n => H0 n
  | Dcmp f dats =>
    let helper := fix F l :=
      match l as l' return Forall P l' with
      | nil => Forall_nil P
      | cons x xs =>
        @Forall_cons _ P x xs (datum_induction P H0 Hind x) (F xs)
      end
    in
    Hind f dats (helper dats)
  end.

(** We need a stronger induction principle that
    the one infered by Coq.
*)
Fixpoint pattern_induction
  (P : pattern -> Prop)
  (H0 : forall c, P (Pcst c))
  (H1 : forall x, P (Pvar x))
  (Hind : forall f dats, Forall P dats -> P (Pcmp f dats))
  (pat : pattern) : P pat :=
  match pat with
  | Pcst n => H0 n
  | Pvar x => H1 x
  | Pcmp f pats =>
    let helper := fix F l :=
      match l as l' return Forall P l' with
      | nil => Forall_nil P
      | cons x xs =>
        @Forall_cons _ P x xs (pattern_induction P H0 H1 Hind x) (F xs)
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
  | Dcst _ => 1
  | Dcmp _ dats =>
    1 + sum datum_size dats
  end.

Fixpoint pattern_size (p : pattern) : nat :=
  match p with
  | Pcst _ => 1
  | Pvar _ => 1
  | Pcmp _ pats =>
    1 + sum pattern_size pats
  end.

(** Boolean equality for [datum] *)
Fixpoint datum_eqb (d1 d2 : datum) : bool :=
  match d1, d2 with
  | Dcst c1, Dcst c2 => (c1 =? c2)%string
  | Dcmp f1 l1, Dcmp f2 l2 =>
    let fix F l1 l2 :=
      match l1, l2 with
      | [], [] => true
      | x::xs, y::ys => andb (datum_eqb x y) (F xs ys)
      | _, _ => false
      end
    in andb (f1 =? f2)%string (F l1 l2)
  | _, _ => false
  end.

Lemma datum_eqb_refl:
  forall x, datum_eqb x x = true.
Proof.
  refine (datum_induction _ _ _); intros; simpl.
  + apply String.eqb_refl.
  + apply Bool.andb_true_iff; split.
    apply String.eqb_refl.
    induction dats; try easy.
    inversion H as [| ? ? H1 H2]; subst.
    rewrite H1. simpl.
    now apply IHdats.
Qed.

Lemma datum_eqb_eq:
  forall x y, datum_eqb x y = true <-> x = y.
Proof.
  refine (datum_induction _ _ _).
  - intros c []; simpl; try easy.
    now rewrite String.eqb_eq; split; intros [=->].
  - intros f dats IH y. split; intros.
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