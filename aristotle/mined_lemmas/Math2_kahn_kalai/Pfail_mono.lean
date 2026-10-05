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

lemma Pfail_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset (Finset α)}
    (hAB : Covers A B) (k : ℕ) : Pfail p k A ≤ Pfail p k B := by
  induction k generalizing A B with
  | zero =>
      rw [Pfail_zero, Pfail_zero]
      unfold failInd
      split_ifs with hA hB hB'
      · exact le_rfl
      · norm_num
      · obtain ⟨S, hS, hSe⟩ := hB'
        obtain ⟨T, hT, hTS⟩ := hAB S hS
        exact absurd ⟨T, hT, hTS.trans hSe⟩ hA
      · exact le_rfl
  | succ k ih =>
      rw [Pfail_succ, Pfail_succ]
      exact Finset.sum_le_sum fun W _ =>
        mul_le_mul_of_nonneg_left (ih (hAB.image_sdiff W)) (weight_nonneg hp0 hp1 W)

omit [Fintype α] in
