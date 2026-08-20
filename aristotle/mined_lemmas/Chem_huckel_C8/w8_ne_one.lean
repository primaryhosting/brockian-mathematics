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

theorem w8_ne_one {d : Fin 8} (hd : d ≠ 0) : w8 d ≠ 1 :=
  zeta8_isPrimitiveRoot.pow_ne_one_of_pos_of_lt
    (fun h => hd (Fin.val_eq_zero_iff.mp h)) d.isLt

/-- Orthogonality relation for the characters of `Fin 8`. -/
