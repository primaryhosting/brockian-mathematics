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

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma zeta19_pow_mod (m : ℕ) : zeta19 ^ m = zeta19 ^ (m % 19) := by
  conv_lhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta19_pow_19, one_pow, one_mul]

