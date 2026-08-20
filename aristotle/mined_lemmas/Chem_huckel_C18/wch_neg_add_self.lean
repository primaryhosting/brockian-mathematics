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

theorem wch_neg_add_self (a : ZMod 18) : wch a * wch (-a) = 1 := by
  rw [← wch_add]; simp [wch_zero]

