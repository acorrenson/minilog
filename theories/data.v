From Coq Require Import String List Program.Wf Arith.
From minilog Require Import utils set.
Import ListNotations.

(** * An simple algebra of first order terms to describe databases *)

(** ** Syntax *)

(** A [datum] is function symbol applied to a set of [datum] *)
Inductive datum :=
  | Dapp : string -> list datum -> datum.

Definition Dcst (c : string) := Dapp c [].

(** Patterns over [datum] *)
Inductive pattern :=
  | Pvar : nat -> pattern
  | Papp : string -> list pattern -> pattern.

Definition Pcst (c : string) := Papp c [].

(** ** Induction Principles *)

(** We need a stronger induction principle that
    the one infered by Coq.
*)
Fixpoint datum_induction
  (P : datum -> Prop)
  (Hind : forall f dats, Forall P dats -> P (Dapp f dats))
  (dat : datum) : P dat :=
  match dat with
  | Dapp f dats =>
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
  (Hind : forall f dats, Forall P dats -> P (Papp f dats))
  (pat : pattern) : P pat :=
  match pat with
  | Pvar x => H1 x
  | Papp f pats =>
    let helper := fix F l :=
      match l as l' return Forall P l' with
      | nil => Forall_nil P
      | cons x xs =>
        @Forall_cons _ P x xs (pattern_induction P H1 Hind x) (F xs)
      end
    in
    Hind f pats (helper pats)
  end.

(** Free variables of a pattern *)
Inductive free_var : pattern -> pset nat :=
| free_var_var x : free_var (Pvar x) x
| free_var_app x f l :
  Exists (fun p => free_var p x) l -> free_var (Papp f l) x.

Fixpoint is_free (p : pattern) (x : nat) : bool :=
  match p with
  | Pvar y => (y =? x)%nat
  | Papp _ pats => existsb (fun p => is_free p x) pats
end.

Lemma is_free_iff:
  forall p x, is_free p x = true <-> free_var p x.
Proof.
  induction p using pattern_induction.
  - intros y. split.
    + intros Hy. simpl in Hy.
      apply Nat.eqb_eq in Hy as ->.
      econstructor.
    + inversion 1; subst. simpl. 
      apply Nat.eqb_refl.
  - intros x. split.
    + simpl.
      intros [pat [Hpat1 Hpat2]]%existsb_exists.
      rewrite Forall_forall in H.
      pose proof (proj1 (H _ Hpat1 _) Hpat2).
      econstructor. apply Exists_exists.
      now exists pat.
    + inversion_clear 1 as [|? ? ? [pat [Hpat1 Hpat2]]%Exists_exists]; subst.
      rewrite Forall_forall in H.
      pose proof (proj2 (H _ Hpat1 _) Hpat2).
      apply existsb_exists.
      now exists pat.
Qed.

Theorem is_free_false:
  forall p x, is_free p x = false -> ~free_var p x.
Proof.
  intros p x H Hcontr.
  apply is_free_iff in Hcontr.
  now rewrite Hcontr in H.
Qed.

Declare Scope datum.
Delimit Scope datum with datum.
Declare Scope pattern.
Delimit Scope pattern with pattern.

Fixpoint datum_size (d : datum) : nat :=
  match d with
  | Dapp _ dats =>
    1 + sum datum_size dats
  end.

Fixpoint pattern_size (p : pattern) : nat :=
  match p with
  | Pvar _ => 1
  | Papp _ pats =>
    1 + sum pattern_size pats
  end.

(** Boolean equality for [datum] *)
Fixpoint datum_eqb (d1 d2 : datum) : bool :=
  match d1, d2 with
  | Dapp f1 l1, Dapp f2 l2 =>
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
    assert (Dapp s dats = Dapp s l).
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