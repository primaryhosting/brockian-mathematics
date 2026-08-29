import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

theorem KL_nonneg {γ : Type*} [Fintype γ] (p q : γ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hac : ∀ i, p i ≠ 0 → q i ≠ 0) : 0 ≤ KL p q := by
  have key : ∀ i, -(p i * Real.log (p i / q i)) ≤ q i - p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | h0
    · simp [← h0, hq i]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (fun hh => hac i (ne_of_gt h0) hh.symm)
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt h0)] at hmul
      calc -(p i * Real.log (p i / q i)) = p i * Real.log (q i / p i) := by
            rw [Real.log_div (ne_of_gt h0) (ne_of_gt hqi),
              Real.log_div (ne_of_gt hqi) (ne_of_gt h0)]
            ring
        _ ≤ q i - p i * 1 := hmul
        _ = q i - p i := by ring
  have hsum : ∑ i, -(p i * Real.log (p i / q i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum (fun i _ => key i)
  rw [Finset.sum_sub_distrib, hps, hqs] at hsum
  simp only [Finset.sum_neg_distrib, KL] at hsum ⊢
  linarith

/-- Mutual information of a joint probability distribution `p` on a product of finite sets:
the KL divergence of the joint from the product of its marginals. -/
