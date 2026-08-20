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

theorem huckel_C20_eigenvector_ne_zero (k : Fin 20) :
    (fun j : Fin 20 => zeta (j * k)) ≠ 0 := by
  intro h
  have h0 : zeta ((0 : Fin 20) * k) = 0 := congrFun h 0
  exact zeta_ne_zero _ h0

end Chem

