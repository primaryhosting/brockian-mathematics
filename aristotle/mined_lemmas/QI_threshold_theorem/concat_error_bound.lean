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

theorem concat_error_bound (c : ℝ) (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n, p (n + 1) ≤ c * (p n) ^ 2) (hc : 0 < c) :
    ∀ L, c * p L ≤ (c * p 0) ^ (2 ^ L) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    have h0 : 0 ≤ c * p L := mul_nonneg hc.le (hp L)
    have h1 : c * p (L + 1) ≤ (c * p L) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hrec L) hc.le
      calc c * p (L + 1) ≤ c * (c * (p L) ^ 2) := this
        _ = (c * p L) ^ 2 := by ring
    have h2 : (c * p L) ^ 2 ≤ ((c * p 0) ^ (2 ^ L)) ^ 2 := by
      exact pow_le_pow_left₀ h0 ih 2
    have h3 : ((c * p 0) ^ (2 ^ L)) ^ 2 = (c * p 0) ^ (2 ^ (L + 1)) := by
      rw [← pow_mul, pow_succ]
    linarith [h1, h2, h3.ge, h3.le]

/--
Below threshold, the logical error rate tends to zero as the concatenation level grows.
-/
