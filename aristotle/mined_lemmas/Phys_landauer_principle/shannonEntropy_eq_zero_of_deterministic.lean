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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- Shannon entropy (in nats) of a probability distribution `p` on a finite type,
`H(p) = -∑ i, p i * log (p i)`, written with Mathlib's `Real.negMulLog`. -/

theorem shannonEntropy_eq_zero_of_deterministic {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, q i = 0 ∨ q i = 1) : shannonEntropy q = 0 := by
  unfold shannonEntropy
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases hq i with h | h <;> simp [h, Real.negMulLog]

/-- The uniform distribution on two states (one bit) has entropy `log 2` nats. -/
