/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma det_vec_ne_zero : C19vec.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det vec_mul_conj
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, ZMod.card] at h
  norm_num at h

/-! ### The characteristic determinant -/

