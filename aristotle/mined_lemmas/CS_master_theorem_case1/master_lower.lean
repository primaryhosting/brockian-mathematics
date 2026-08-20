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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- `((b:ℝ)^k) ^ (log_b a) = a ^ k` (outer exponent is a real power). -/

lemma master_lower (ha : 0 < a) (hfnn : ∀ n : ℕ, 0 ≤ f n)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) (k : ℕ) :
    a ^ k * T 1 ≤ T (b ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := hrec k
      have : a * (a ^ k * T 1) ≤ a * T (b ^ k) := by
        exact mul_le_mul_of_nonneg_left ih ha.le
      have hf := hfnn (b ^ (k + 1))
      calc a ^ (k + 1) * T 1 = a * (a ^ k * T 1) := by ring
        _ ≤ a * T (b ^ k) := this
        _ ≤ a * T (b ^ k) + f (b ^ (k + 1)) := by linarith
        _ = T (b ^ (k + 1)) := h.symm

/-- Strengthened upper bound used for the induction. -/
