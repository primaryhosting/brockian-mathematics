import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₂H₁₂` uses the adjacency matrix of the cycle
graph `C₁₂`.  We show that the characteristic polynomial of this adjacency matrix is
`∏ k, (X - 2 cos (2πk/12))`, and consequently that the eigenvalues of the adjacency matrix
are exactly the numbers `2 cos (2πk/12)`, `k = 0, …, 11`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ω ^ (j * k)`, where `ω = exp (2πi/12)`.
-/

namespace Chem

open Complex Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₁₂`, viewed over `ℂ`. -/

lemma charpoly_adjC12 :
    adjC12.charpoly = ∏ k : Fin 12, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  have hdet : IsUnit dftF.det := isUnit_iff_ne_zero.mpr dftF_det_ne_zero
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det dftF).mpr hdet
  have hA : adjC12 = U.val * eigD * (U⁻¹).val := by
    rw [Matrix.coe_units_inv, hU, ← adjC12_mul_dftF, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  rw [hA, Matrix.charpoly_units_conj U eigD, eigD, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₁₂`.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₂` is `∏ k, (X - 2 cos (2πk/12))`; equivalently, the eigenvalues of the
adjacency matrix are exactly the numbers `2 cos (2πk/12)` for `k = 0, …, 11`. -/
