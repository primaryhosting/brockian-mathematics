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

theorem ee_mul (k d : Fin 19) : ee (k * d) = ee d ^ (k : ℕ) := by
  simp only [ee, Fin.val_mul, om_pow_mod, pow_mul]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

