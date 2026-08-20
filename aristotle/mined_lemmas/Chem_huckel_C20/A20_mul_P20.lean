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

lemma A20_mul_P20 : A20 * P20 = P20 * Matrix.diagonal ev := by
  ext i k
  have h : (A20 * P20) i k = (A20 *ᵥ (fun j : Fin 20 => zeta (j * k))) i := by
    rw [Matrix.mul_apply]; rfl
  rw [h, A20_mulVec_fourier, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

