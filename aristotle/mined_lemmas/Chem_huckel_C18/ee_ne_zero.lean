import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma ee_ne_zero (a : ZMod 18) : ee a ≠ 0 := by
  have : ee a * ee (-a) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  intro h
  rw [h, zero_mul] at this
  exact zero_ne_one this

