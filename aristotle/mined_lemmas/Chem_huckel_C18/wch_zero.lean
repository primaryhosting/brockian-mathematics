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

theorem wch_zero : wch 0 = 1 := by simp [wch]

