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

/-- A primitive 16-th root of unity. -/

lemma zeta_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 16]
  conv_rhs => rw [← Nat.div_add_mod b 16]
  simp [pow_add, pow_mul, zeta_pow_sixteen, h]

