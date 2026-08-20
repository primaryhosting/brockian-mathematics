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

lemma zeta_neg (a : Fin 20) : zeta (-a) = (zeta a)⁻¹ := by
  have h : zeta (-a) * zeta a = 1 := by rw [← zeta_add]; simp [zeta_zero]
  exact eq_inv_of_mul_eq_one_left h

