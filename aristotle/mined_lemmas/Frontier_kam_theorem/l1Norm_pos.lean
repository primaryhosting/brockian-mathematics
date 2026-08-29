import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma l1Norm_pos {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < l1Norm k := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext fun j => h j)
  have h1 : (0 : ℝ) < |(k j : ℝ)| := by
    simpa [abs_pos] using (Int.cast_ne_zero (α := ℝ)).2 hj
  exact lt_of_lt_of_le h1 (abs_le_l1Norm k j)

/-! ### Small divisor estimates -/

