/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The Möbius function at `6` equals `1` (since `6 = 2 * 3` is squarefree with two prime
factors). -/

theorem cyclotomic_six_eq_zero_of_isPrimitiveRoot {z : ℂ} (h : IsPrimitiveRoot z 6) :
    z ^ 2 - z + 1 = 0 := by
  have h6 : z ^ 6 = 1 := h.pow_eq_one
  have h2 : z ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h3 : z ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have key : (z ^ 2 - 1) * (z ^ 2 + z + 1) * (z ^ 2 - z + 1) = 0 := by
    linear_combination h6
  rcases mul_eq_zero.1 key with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd (by linear_combination h'' : z ^ 2 = 1) h2
    · exact absurd (by linear_combination (z - 1) * h'' : z ^ 3 = 1) h3
  · exact h'

/-- The set of primitive `6`-th roots of unity in `ℂ` consists of exactly `z` and `z ^ 5`,
for any primitive `6`-th root of unity `z`. -/
