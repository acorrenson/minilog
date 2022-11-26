Declare Scope ops.
Delimit Scope ops with ops.

Class InOp (x X : Type) :=
  in_op_ : x -> X -> Prop.

Notation "x ∈ X" := (in_op_ x X) (at level 39) : ops.

Class CupOp (A : Type) :=
  cup_op_ : A -> A -> A.

Notation "x ∪ y" := (cup_op_ x y) (at level 40) : ops.

Class CapOp (A : Type) :=
  cap_op_ : A -> A -> A.

Notation "x ∩ y" := (cap_op_ x y) (at level 40) : ops.

Class SubsetOp (A : Type) :=
  subset_op_ : A -> A -> Prop.

Notation "x ⊂ y" := (subset_op_ x y) (at level 39) : ops.

Class SubseteqOp (A : Type) :=
  subseteq_op_ : A -> A -> Prop.

Notation "x ⊆ y" := (subseteq_op_ x y) (at level 39) : ops.