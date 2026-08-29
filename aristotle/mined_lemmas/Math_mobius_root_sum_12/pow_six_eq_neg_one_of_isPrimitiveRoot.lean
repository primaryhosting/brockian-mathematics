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
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `ζ` is a primitive 12-th root of unity in `ℂ`, then `ζ ^ 6 = -1`. -/

lemma pow_six_eq_neg_one_of_isPrimitiveRoot {ζ : ℂ} (h : IsPrimitiveRoot ζ 12) :
    ζ ^ 6 = -1 := by
  have h12 : (ζ ^ 6) * (ζ ^ 6) = 1 := by
    rw [← pow_add]
    exact h.pow_eq_one
  rcases mul_self_eq_one_iff.1 h12 with h1 | h1
  · exact absurd ((h.pow_eq_one_iff_dvd 6).1 h1) (by decide)
  · exact h1

/-- The negative of a primitive 12-th root of unity is again a primitive 12-th root of
unity, since `-ζ = ζ ^ 7` and `7` is coprime to `12`. -/
