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

theorem wch_eq_exp (a : ZMod 18) :
    wch a = Complex.exp ((2 * Real.pi * a.val / 18 : ℝ) * Complex.I) := by
  rw [wch, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/18)`. -/
