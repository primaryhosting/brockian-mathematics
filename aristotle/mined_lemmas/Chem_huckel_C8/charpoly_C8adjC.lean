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

set_option grind.warning false

namespace Chem

open Polynomial

/-- A primitive 8-th root of unity. -/

theorem charpoly_C8adjC :
    C8adjC.charpoly = ∏ k : Fin 8, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  have hA : C8adjC = dftUnit.val * eigDiag * (dftUnit⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ).val := by
    show C8adjC = dftMat * eigDiag * dftInv
    rw [← C8adjC_mul_dftMat, mul_assoc, dftMat_mul_dftInv, mul_one]
  rw [hA, Matrix.charpoly_units_conj, eigDiag, Matrix.charpoly_diagonal]

/-! ### The main theorem -/

/-- **Hückel theory for the cycle `C₈`.**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₈` is
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`; that is, the adjacency eigenvalues of `C₈`
are `2 cos (2πk/8)` for `k = 0, …, 7`. -/
