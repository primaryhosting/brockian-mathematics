/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem charpoly_adjC9 : adjC9.charpoly = ∏ k : ZMod 9, (X - C (ff k + ff (-k))) := by
  have hu : IsUnit fourier9.det := isUnit_iff_ne_zero.mpr fourier9_det_ne_zero
  set U : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ := fourier9.nonsingInvUnit hu with hU
  have hUv : (U : Matrix (ZMod 9) (ZMod 9) ℂ) = fourier9 := rfl
  have hUi : ((U⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) = fourier9⁻¹ :=
    rfl
  have key : adjC9 = (U : Matrix (ZMod 9) (ZMod 9) ℂ) * diagC9 *
      ((U⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) := by
    rw [hUv, hUi, ← adjC9_mul_fourier9, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
  rw [key, Matrix.charpoly_units_conj, diagC9, Matrix.charpoly_diagonal]

/-- **Hückel theory for the C₉ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₉` factors as `∏_{k=0}^{8} (X - 2 cos (2πk/9))`; equivalently,
the adjacency eigenvalues of `C₉` are `2 cos (2πk/9)` for `k = 0, …, 8`. -/
