/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

lemma e_mul_e_neg (k : ZMod 5) : e k * e (-k) = 1 := by
  rw [← e_add]; simp [e_zero]

