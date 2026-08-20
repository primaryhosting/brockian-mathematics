/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem ee_eq_exp (k : Fin 19) :
    ee k = Complex.exp ((2 * Real.pi * (k : ℕ) / 19 : ℝ) * I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

