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

theorem zeta8_pow_mod (n : ℕ) : zeta8 ^ (n % 8) = zeta8 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

