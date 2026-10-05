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

lemma flipAt_comm {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [flipAt_self, flipAt_ne]

/-- Connectivity of the hypercube: a predicate preserved by all flips in a set `S` of
coordinates propagates between any two points differing only inside `S`. -/
