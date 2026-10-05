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

lemma ee_nsmul (c : ZMod 18) (n : ℕ) : ee (n • c) = ee c ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih => rw [succ_nsmul, ee_add, ih, pow_succ]

