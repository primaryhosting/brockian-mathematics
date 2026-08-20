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

lemma zeta_eq_one_iff (c : Fin 20) : zeta c = 1 ↔ c = 0 := by
  constructor
  · intro h
    have := (w_primitive.pow_eq_one_iff_dvd (c : ℕ)).1 h
    have hlt : (c : ℕ) < 20 := c.isLt
    have : (c : ℕ) = 0 := by
      rcases this with ⟨m, hm⟩
      omega
    exact Fin.ext this
  · rintro rfl; exact zeta_zero

/-- Orthogonality of characters. -/
