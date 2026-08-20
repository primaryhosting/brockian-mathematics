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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace CS

/-- `(b^k)^(log_b a) = a^k`. -/

lemma geom_sum_le_inv_one_sub (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r ^ j ≤ (1 - r)⁻¹ := by
  have h1 : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq h1]
  have hpos : 0 < 1 - r := by linarith
  have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
  rw [div_le_iff_of_neg (by linarith : r - 1 < 0)]
  have h2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have h3 : (1 - r)⁻¹ * (r - 1) = -1 := by linear_combination -h2
  linarith

/-- **Master theorem, case 1.**  Suppose `T` satisfies the divide-and-conquer recurrence
`T n = a * T (n / b) + f n` (formalised along the powers of `b`, where the division is exact),
with `a ≥ 1`, `b ≥ 2`, a nonnegative driving function `f` satisfying
`f n = O (n ^ (log_b a - ε))` for some `ε > 0`, and positive base value `T 1`.
Then `T n = Θ (n ^ (log_b a))` along the powers of `b`: there are positive constants
`c₁, c₂` with `c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
