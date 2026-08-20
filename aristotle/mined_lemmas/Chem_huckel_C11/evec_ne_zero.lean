/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma evec_ne_zero (k : ZMod 11) : evec k ≠ 0 := by
  intro h
  have : evec k 0 = 0 := by rw [h]; rfl
  rw [evec, mul_zero, eps_zero] at this
  exact one_ne_zero this

