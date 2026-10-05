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

lemma e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have := norm_e k
  rw [h] at this
  simp at this

