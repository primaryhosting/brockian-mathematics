import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A *constraint graph* (a binary constraint satisfaction instance): `n` variables taking
values in the alphabet `Fin (q+1)`, together with a list of binary constraints, each given by
an ordered pair of variables and a decidable relation on the alphabet. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- The alphabet is `Fin (q+1)`; in particular it is nonempty. -/
  q : ℕ
  /-- The constraints: each is a pair of variables together with a relation they must satisfy. -/
  edges : List ((Fin n × Fin n) × (Fin (q + 1) → Fin (q + 1) → Bool))

namespace ConstraintGraph

/-- An assignment of alphabet values to the variables of `G`. -/
abbrev Assignment (G : ConstraintGraph) := Fin G.n → Fin (G.q + 1)

/-- The number of constraints of `G` (its size). -/

lemma falseGraph_not_satisfiable : ¬ falseGraph.Satisfiable := by
  simp [satisfiable_iff_minUnsat_eq_zero]

end ConstraintGraph

open ConstraintGraph

/-- The key recursion in Dinur's proof: iterating a gap-doubling amplification step `t` times
multiplies the unsat value by `2 ^ t`, until it saturates at `α`. -/
