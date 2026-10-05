import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The Möbius function vanishes at `12`, since `12 = 2 ^ 2 * 3` is not squarefree. -/

lemma pow_six_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 12) : z ^ 6 = -1 := by
  have h1 : z ^ 12 = 1 := hz.pow_eq_one
  have h2 : z ^ 6 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h3 : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · linear_combination h

/-- The negative of a primitive `12`-th root of unity is again a primitive `12`-th root of
unity (it is the `7`-th power of the original root). -/
