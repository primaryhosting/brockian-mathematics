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

noncomputable def w8 (m : Fin 8) : ℂ := zeta8 ^ m.val

/-- The `k`-th Hückel eigenvalue of the cycle `C₈`, namely `2 cos (2πk/8)`. -/
