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

lemma e_neg (k : ZMod 5) : e (-k) = (e k)⁻¹ := by
  have h : e (-k) * e k = 1 := by rw [← e_add]; simp [e_zero]
  field_simp [e_ne_zero k] at h ⊢
  linear_combination h

