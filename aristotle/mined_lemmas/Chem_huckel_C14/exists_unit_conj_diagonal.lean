/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

lemma exists_unit_conj_diagonal : ∃ u : (Matrix (Fin 14) (Fin 14) ℂ)ˣ,
    SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)
      = (u : Matrix (Fin 14) (Fin 14) ℂ) * Matrix.diagonal eigval
          * (↑u⁻¹ : Matrix (Fin 14) (Fin 14) ℂ) := by
  have hdet : IsUnit (dftMat).det := isUnit_iff_ne_zero.mpr dftMat_det_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det dftMat).mpr hdet
  refine ⟨u, ?_⟩
  rw [Matrix.coe_units_inv, hu, ← adj_mul_dft, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv dftMat hdet, Matrix.mul_one]

/-- **Hückel theory for the annulene C₁₄.**  The spectrum of the adjacency matrix of the cycle
graph `C₁₄` is exactly `{2 cos (2πk/14) : k = 0, …, 13}`. -/
