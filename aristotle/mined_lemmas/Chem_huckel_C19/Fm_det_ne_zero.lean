import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma Fm_det_ne_zero : Fm.det ≠ 0 := by
  intro h
  have h1 : (Fm * Gm).det = 0 := by rw [Matrix.det_mul, h, zero_mul]
  rw [Fm_mul_Gm, Matrix.det_smul, Matrix.det_one, mul_one] at h1
  simp at h1

