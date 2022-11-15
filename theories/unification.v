From Coq Require Import String List Arith Lia.
From minilog Require Import data utils.
Import ListNotations.

(** * Verified Unification Algorithm *)

(** As for matching, a state of the algorithm is a list of equations to be solved and a current solution.
    The only difference is that unification equations are of the form [(pattern, pattern)]
    Solutions are represented as finite maps from variables to patterns ([pattern])
*)
Record state := {
  equations : list (pattern * pattern);
  solution  : @fin_map pattern;
}.