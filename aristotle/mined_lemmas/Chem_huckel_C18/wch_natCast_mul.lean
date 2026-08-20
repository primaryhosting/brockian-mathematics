/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem wch_natCast_mul (n : ℕ) (c : ZMod 18) : wch ((n : ZMod 18) * c) = wch c ^ n := by
  induction n with
  | zero => simp [wch_zero]
  | succ m ih =>
      have : ((m + 1 : ℕ) : ZMod 18) * c = (m : ZMod 18) * c + c := by push_cast; ring
      rw [this, wch_add, ih, pow_succ]

