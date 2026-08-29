import Mathlib
/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

variable {A X : Type*} [Fintype A] [Fintype X]

/-- Expected cost of the mixed (randomized) algorithm strategy `q` on the input `x`. -/

lemma randomized_le_distributional [Nonempty A] [Nonempty X] [DecidableEq A] [DecidableEq X]
    (cost : A → X → ℝ) :
    randomizedComplexity cost ≤ distributionalComplexity cost := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨p, hp, hple⟩ := exists_hard_distribution cost hc2
  have h1 : c ≤ ⨅ a, avgCost cost p a := le_ciInf hple
  have h2 : (⨅ a, avgCost cost p a) ≤ distributionalComplexity cost :=
    le_csSup (distributionalSet_bddAbove cost) ⟨p, hp, rfl⟩
  linarith

/-- **Yao's minimax principle**: for a finite cost matrix `cost : A → X → ℝ`, the randomized
complexity (the least worst-case expected cost of a distribution over deterministic algorithms)
equals the distributional complexity (the greatest over input distributions of the least
expected cost of a deterministic algorithm). -/
