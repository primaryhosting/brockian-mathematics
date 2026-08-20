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

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

theorem w_pow_congr {a b : ℕ} (h : a % 15 = b % 15) : w ^ a = w ^ b := by
  have key : ∀ m : ℕ, w ^ m = w ^ (m % 15) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 15]
    rw [pow_add, pow_mul, w_pow_15, one_pow, one_mul]
  rw [key a, key b, h]

