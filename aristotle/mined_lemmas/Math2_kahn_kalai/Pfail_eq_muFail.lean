import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma Pfail_eq_muFail (p : ℝ) (k : ℕ) (H : Finset (Finset α)) :
    Pfail p k H = muFail (1 - (1 - p) ^ k) H := by
  induction k generalizing H with
  | zero =>
      rw [Pfail_zero, muFail]
      simp only [pow_zero, sub_self]
      rw [Finset.sum_eq_single (∅ : Finset α)]
      · rw [weight_zero, if_pos rfl, one_mul]
      · intro U _ hU
        rw [weight_zero, if_neg hU, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ k ih =>
      rw [Pfail_succ]
      have h1 : ∀ W : Finset α, Pfail p k (H.image (fun S => S \ W))
          = ∑ V : Finset α, weight (1 - (1 - p) ^ k) V * failInd H (W ∪ V) := by
        intro W
        rw [ih, muFail]
        exact Finset.sum_congr rfl fun V _ => by rw [failInd_image_sdiff]
      calc ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W))
          = ∑ W : Finset α, ∑ V : Finset α,
              weight p W * weight (1 - (1 - p) ^ k) V * failInd H (W ∪ V) := by
            refine Finset.sum_congr rfl fun W _ => ?_
            rw [h1 W, Finset.mul_sum]
            exact Finset.sum_congr rfl fun V _ => by ring
        _ = ∑ U : Finset α,
              weight (1 - (1 - p) * (1 - (1 - (1 - p) ^ k))) U * failInd H U :=
            sum_union_weight _ _ _
        _ = muFail (1 - (1 - p) ^ (k + 1)) H := by
            have hpow : 1 - (1 - p) * (1 - (1 - (1 - p) ^ k)) = 1 - (1 - p) ^ (k + 1) := by
              ring
            rw [muFail, hpow]

/-- Monotonicity of the failure probability in `p`. -/
