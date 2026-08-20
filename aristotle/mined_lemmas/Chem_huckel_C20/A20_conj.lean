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

open Complex Polynomial Matrix

/-- The commutative ring structure on `Fin 20 = ZMod 20`, used for index arithmetic. -/
noncomputable instance : CommRing (Fin 20) := inferInstanceAs (CommRing (ZMod 20))

/-- A primitive 20-th root of unity. -/

lemma A20_conj : A20 = (U20 : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal ev
    * ((U20⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
  have hP : ((U20 : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = P20 := rfl
  have hQ : ((U20⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = Q20 := rfl
  rw [hP, hQ, ← A20_mul_P20, mul_assoc, P20_mul_Q20, mul_one]

/-- **Hückel theory for C₂₀.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` is `∏ k < 20, (X - 2 cos (2πk/20))`; i.e. the adjacency eigenvalues of `C₂₀`
are exactly the numbers `2 cos (2πk/20)`, `k = 0, …, 19`. -/
