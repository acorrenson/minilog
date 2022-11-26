Require Import minilog.operators.

(** * Operations over sets *)

Section Pset.

Variable A : Type.

Definition pset := (A -> Prop).

Definition inter (P Q : pset) : pset :=
  fun x => P x /\ Q x.

Definition union (P Q : pset) : pset :=
  fun x => P x \/ Q x.

Definition diff (P Q : pset) : pset :=
  fun x => P x /\ ~Q x.

Definition comp (P : pset) : pset :=
  fun x => ~P x.

Definition subseteq (P Q : pset) :=
  forall x, P x -> Q x.

Definition subset (P Q : pset) :=
  subseteq P Q /\ exists x, Q x /\ ~Q x.

Definition emptyset : pset := fun _ => False.

End Pset.

Instance inter_cap (A : Type) : CapOp (pset A) := inter A.
Instance union_cup (A : Type) : CupOp (pset A) := union A.
Instance subseteq_subseteq (A : Type) : SubseteqOp (pset A) := subseteq A.
Instance subset_subset (A : Type) : SubsetOp (pset A) := subset A.
Notation "∅" := (emptyset _).