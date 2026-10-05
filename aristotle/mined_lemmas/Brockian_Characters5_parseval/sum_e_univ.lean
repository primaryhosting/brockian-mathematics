/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_e_univ : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ a : ZMod 5, e a = ∑ j ∈ Finset.range 5, omega ^ j := by
    simp only [e]
    rfl
  rw [h, sum_omega_pow_range]

/-- Orthogonality of the character `e`. -/
