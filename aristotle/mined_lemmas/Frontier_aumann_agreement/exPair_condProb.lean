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

private theorem exPair_condProb {a b c : Fin 4} {E : Finset (Fin 4)} (hab : a ≠ b)
    (h : ({a, b} : Finset (Fin 4)) ∩ E = {c}) :
    condProb exPrior E {a, b} = 1 / 2 := by
  rw [condProb, h, Finset.sum_singleton, Finset.sum_pair hab]
  simp only [exPrior]
  norm_num

