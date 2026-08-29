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

lemma sum_omega_pow_range : ∑ j ∈ Finset.range 5, omega ^ j = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

