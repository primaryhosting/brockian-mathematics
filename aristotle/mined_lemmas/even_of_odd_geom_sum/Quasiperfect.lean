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


def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

/-- For an odd `p`, the geometric sum `1 + p + ⋯ + p ^ e` is odd iff `e` is even. -/
