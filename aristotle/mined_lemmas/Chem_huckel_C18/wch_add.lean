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

theorem wch_add (a b : ZMod 18) : wch (a + b) = wch a * wch b := by
  rw [wch, wch, wch, ← pow_add]
  exact zeta_pow_congr (by rw [ZMod.val_add]; simp [Nat.mod_mod_of_dvd])

