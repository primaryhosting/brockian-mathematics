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

lemma w_pow_20 : w ^ (20 : ℕ) = 1 := w_primitive.pow_eq_one

