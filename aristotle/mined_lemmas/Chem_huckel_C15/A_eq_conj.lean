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

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

theorem A_eq_conj : A = (F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ) * D
    * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) : Matrix (Fin 15) (Fin 15) ℂ) := by
  have hu : (F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ) = F := F_isUnit.unit_spec
  calc A = A * ((F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ)
            * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
              Matrix (Fin 15) (Fin 15) ℂ)) := by rw [Units.mul_inv, mul_one]
    _ = (A * F) * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
            Matrix (Fin 15) (Fin 15) ℂ) := by rw [← mul_assoc, hu]
    _ = (F * D) * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
            Matrix (Fin 15) (Fin 15) ℂ) := by rw [A_mul_F]
    _ = _ := by rw [hu]

