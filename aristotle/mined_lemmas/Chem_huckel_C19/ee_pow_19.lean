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

theorem ee_pow_19 (d : Fin 19) : ee d ^ (19 : ℕ) = 1 := by
  rw [ee, ← pow_mul, Nat.mul_comm, pow_mul, om_pow_19, one_pow]

