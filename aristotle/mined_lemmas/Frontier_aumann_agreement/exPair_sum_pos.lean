import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The conditional probability of the event `E` given the (information) cell `C`,
computed from the weight function `p`. -/

private theorem exPair_sum_pos {a b : Fin 4} (hab : a ≠ b) :
    0 < ∑ y ∈ ({a, b} : Finset (Fin 4)), exPrior y := by
  rw [Finset.sum_pair hab]
  simp only [exPrior]
  norm_num

/-- The hypotheses of `Frontier.aumann_agreement` are satisfiable in a nontrivial situation:
two agents with genuinely different (and incomparable) information partitions on a four-state
space, whose common-knowledge component is the whole space, both assign probability `1/2`
to the event `{0, 2}`. -/
