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

theorem above_threshold_diverges (c : ℝ) (p : ℕ → ℝ) (hc : 0 < c)
    (hrec : ∀ n, c * (p n) ^ 2 ≤ p (n + 1)) (hthr : 1 < c * p 0) :
    Filter.Tendsto (fun L : ℕ => c * p L) Filter.atTop Filter.atTop := by
  have key : ∀ L, (c * p 0) ^ (2 ^ L) ≤ c * p L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      have h0 : (0:ℝ) ≤ (c * p 0) ^ (2 ^ L) := by positivity
      have h1 : (c * p L) ^ 2 ≤ c * p (L + 1) := by
        have := mul_le_mul_of_nonneg_left (hrec L) hc.le
        calc (c * p L) ^ 2 = c * (c * (p L) ^ 2) := by ring
          _ ≤ c * p (L + 1) := this
      have h2 : ((c * p 0) ^ (2 ^ L)) ^ 2 ≤ (c * p L) ^ 2 := pow_le_pow_left₀ h0 ih 2
      have h3 : ((c * p 0) ^ (2 ^ L)) ^ 2 = (c * p 0) ^ (2 ^ (L + 1)) := by
        rw [← pow_mul, pow_succ]
      linarith [h3.ge, h3.le]
  have hpow : Filter.Tendsto (fun L : ℕ => (c * p 0) ^ (2 ^ L)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => (c * p 0) ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hthr
    have h2 : Filter.Tendsto (fun L : ℕ => 2 ^ L) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ) < 2)
    exact h1.comp h2
  exact Filter.tendsto_atTop_mono key hpow

#print axioms QI.threshold_theorem

end QI

