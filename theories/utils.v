From Coq Require Import List Arith Lia.
Import ListNotations.

(** * Usefull functions and definitions *)

(** ** Error Monad *)

Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
  | None => None
  | Some y => f y
  end.

Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).

(** ** Finite Maps as association lists *)

Definition fin_map A := list (nat * A).

Fixpoint get {A} (f : fin_map A) (n : nat) :=
  match f with
  | [] => None
  | (x, vx)::xs => 
    if (x =? n)%nat then Some vx else get xs n
  end.

Definition set {A} (f : fin_map A) (x : nat) (vx : A) :=
  (x, vx)::f.

Lemma get_set:
  forall A (f : fin_map A) (x : nat) (vx : A),
    get (set f x vx) x = Some vx.
Proof.
  intros. simpl.
  now rewrite Nat.eqb_refl.
Qed.

Lemma get_in:
  forall A m x (vx : A), get m x = Some vx -> In (x, vx) m.
Proof.
  induction m as [|[x vx] m IH]; intros y vy; simpl in *; try easy.
  destruct Nat.eqb eqn:Heq.
  + apply Nat.eqb_eq in Heq as ->. intros [=->].
    now left.
  + intros H%IH. now right.
Qed.

Lemma in_get:
  forall A m x (vx : A), In (x, vx) m -> get m x <> None.
Proof.
  induction m as [|[x vx] m IH]; intros y vy; simpl in *; try easy.
  destruct Nat.eqb eqn:Heq.
  + apply Nat.eqb_eq in Heq as ->. now intros [[=->]| H].
  + intros [[=->]| H]. now rewrite Nat.eqb_refl in Heq.
    eapply IH, H.
Qed.

(** ** Indexed Sums *)

Definition sum_aux {A} (f : A -> nat) (l : list A) (n : nat) :=
  fold_left (fun x y => x + f y) l n.

Definition sum {A} (f : A -> nat) (l : list A) :=
  sum_aux f l 0.

Lemma sum_aux_mono:
  forall A (l : list A) f p q,
    p < q -> sum_aux f l p < sum_aux f l q.
Proof.
  induction l as [| x xs IH]; intros; simpl; auto.
  apply IH. lia.
Qed.

Lemma sum_aux_add:
  forall A (l : list A) f p q,
    sum_aux f l (p + q) = sum_aux f l p + q.
Proof.
  induction l as [| x xs IH]; intros; simpl; auto.
  repeat rewrite IH. lia.
Qed.

Lemma sum_cons :
  forall A (x : A) (l : list A) f,
    sum f (x::l) = f x + sum f l.
Proof.
  intros. unfold sum, sum_aux.
  fold ([x] ++ l).
  rewrite fold_left_app. simpl.
  fold (sum_aux f l (f x)).
  fold (0 + f x). rewrite sum_aux_add.
  unfold sum_aux. lia.
Qed.

Lemma sum_app :
  forall A (l1 l2 : list A) f,
    sum f (l1 ++ l2) = (sum f l1) + (sum f l2).
Proof.
  intros. unfold sum at 1, sum_aux at 1.
  rewrite fold_left_app.
  fold (sum_aux f l1 0).
  fold (sum_aux f l2 (sum_aux f l1 0)).
  fold (Nat.add 0 (sum_aux f l1 0)).
  rewrite sum_aux_add.
  fold (sum f l2).
  fold (sum f l1).
  lia.
Qed.