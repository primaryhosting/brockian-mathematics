import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma gibbs_sum [Nonempty B] (beta : ℝ) (E : B → ℝ) : ∑ b : B, gibbs beta E b = 1 := by
  unfold gibbs
  rw [← Finset.sum_div, div_self (ne_of_gt (gibbs_partition_pos beta E))]

