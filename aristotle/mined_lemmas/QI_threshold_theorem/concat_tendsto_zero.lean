/-
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
Doubly exponential suppression of the logical error rate under concatenation.

If the level-`n` logical failure probabilities `p n` of a fault-tolerant scheme obey the
standard concatenation recursion `p (n+1) ≤ c * (p n)^2` (a level-`(n+1)` block fails only
if at least two of its `≈ c` malignant level-`n` locations fail), then

  `c * p L ≤ (c * p 0) ^ (2 ^ L)`.
-/

theorem concat_tendsto_zero (c : ℝ) (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n, p (n + 1) ≤ c * (p n) ^ 2) (hc : 0 < c) (hthr : c * p 0 < 1) :
    Filter.Tendsto p Filter.atTop (nhds 0) := by
  set q : ℝ := c * p 0 with hq
  have hq0 : 0 ≤ q := mul_nonneg hc.le (hp 0)
  have hbound := concat_error_bound c p hp hrec hc
  have hpow : Filter.Tendsto (fun L : ℕ => q ^ (2 ^ L)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hthr
    have h2 : Filter.Tendsto (fun L : ℕ => 2 ^ L) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ) < 2)
    exact h1.comp h2
  have hlim : Filter.Tendsto (fun L : ℕ => c⁻¹ * q ^ (2 ^ L)) Filter.atTop (nhds 0) := by
    have := hpow.const_mul c⁻¹
    simpa using this
  refine squeeze_zero hp (fun n => ?_) hlim
  have hb := hbound n
  rw [← hq] at hb
  have hkey : c⁻¹ * (c * p n) ≤ c⁻¹ * q ^ 2 ^ n :=
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
  calc p n = c⁻¹ * (c * p n) := by field_simp
    _ ≤ c⁻¹ * q ^ 2 ^ n := hkey

/--
**Threshold theorem for fault-tolerant quantum computation.**

Consider a concatenated fault-tolerant scheme whose level-`n` logical failure probability
`p n` satisfies the concatenation recursion `p (n+1) ≤ c * (p n)^2`, where `c > 0` counts
the malignant pairs of locations in a level-1 rectangle.  If the physical error rate is
*below the threshold* `1 / c`, i.e. `c * p 0 < 1`, then:

1. the logical error rate is doubly exponentially suppressed:
   `c * p L ≤ (c * p 0) ^ (2 ^ L)`;
2. the logical error rate tends to `0` as the level of concatenation grows;
3. hence for every target accuracy `ε > 0` there is a concatenation level `L` beyond which
   the logical error rate is below `ε`, i.e. arbitrarily reliable (fault-tolerant) quantum
   computation is possible.
-/
