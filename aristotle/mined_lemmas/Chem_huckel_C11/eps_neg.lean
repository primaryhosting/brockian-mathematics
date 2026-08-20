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

lemma eps_neg (x : ZMod 11) : eps (-x) = (eps x)⁻¹ := by
  have h : eps (-x) * eps x = 1 := by rw [← eps_add]; simp [eps_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- The value of `eps` in terms of the exponential. -/
