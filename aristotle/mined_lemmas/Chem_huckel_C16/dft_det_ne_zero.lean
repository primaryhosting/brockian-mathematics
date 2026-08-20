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

/-- A primitive 16-th root of unity. -/

lemma dft_det_ne_zero : (dftMat).det ≠ 0 := by
  have hvan : dftMat = Matrix.vandermonde (fun i : Fin 16 => zeta ^ (i : ℕ)) := by
    ext i k
    simp [dftMat, Matrix.vandermonde, ← pow_mul]
  rw [hvan, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- The adjacency matrix of `C₁₆` is conjugate (by the discrete Fourier matrix) to the
diagonal matrix of the values `2 cos (2πk/16)`. -/
