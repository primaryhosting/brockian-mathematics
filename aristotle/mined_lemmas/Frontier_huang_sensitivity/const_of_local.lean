/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma const_of_local {n : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ∀ x i, f (flipAt x i) = f x) : ∀ x y, f x = f y := by
  intro x y
  refine cube_connected (P := fun z => f x = f z) (S := Finset.univ) ?_ x y (by simp) rfl
  intro z j _ hz
  show f x = f (flipAt z j)
  rw [h z j]
  exact hz

/-! ## Character sums -/

/-- Orthogonality of characters, summed over the sets: `∑_S χ_S(x) χ_S(y)` is `2^n`
if `x = y` and `0` otherwise. -/
