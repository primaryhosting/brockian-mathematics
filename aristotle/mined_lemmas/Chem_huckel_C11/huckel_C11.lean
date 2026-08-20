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

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/

theorem huckel_C11 :
    ((cycleGraph 11).adjMatrix ℂ).charpoly =
      ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ)) := by
  have hGF : Gm * Fm = 1 := mul_eq_one_comm.mp Fm_mul_Gm
  have hA : (cycleGraph 11).adjMatrix ℂ = Fm * (Dm * Gm) := by
    rw [← Matrix.mul_assoc, ← adjMatrix_mul_Fm, Matrix.mul_assoc, Fm_mul_Gm, Matrix.mul_one]
  rw [hA, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hGF, Matrix.mul_one]
  simpa [Dm] using Matrix.charpoly_diagonal
    (fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ))

/-- **Hückel spectrum of the cycle `C₁₁`, as a set.**  The eigenvalues of the adjacency matrix
of `C₁₁` are exactly the numbers `2 cos (2πk/11)`, `k = 0, …, 10`. -/
