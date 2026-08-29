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

lemma Pfail_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (H : Finset (Finset α)) :
    Pfail p k H ≤ 1 := by
  induction k generalizing H with
  | zero => rw [Pfail_zero]; exact failInd_le_one _ _
  | succ k ih =>
      rw [Pfail_succ]
      calc ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W))
          ≤ ∑ W : Finset α, weight p W * 1 := by
            refine Finset.sum_le_sum fun W _ => ?_
            exact mul_le_mul_of_nonneg_left (ih _) (weight_nonneg hp0 hp1 W)
        _ = 1 := by simpa using sum_weight (α := α) p

omit [Fintype α] in
