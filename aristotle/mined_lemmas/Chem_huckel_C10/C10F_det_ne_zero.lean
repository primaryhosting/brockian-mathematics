import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem C10F_det_ne_zero : C10F.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det C10F_mul_C10G
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

