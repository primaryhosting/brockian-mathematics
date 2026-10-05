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

lemma distributional_le_randomized [Nonempty A] [Nonempty X] [DecidableEq A] [DecidableEq X]
    (cost : A → X → ℝ) :
    distributionalComplexity cost ≤ randomizedComplexity cost := by
  apply csSup_le (distributionalSet_nonempty cost)
  rintro y ⟨p, hp, rfl⟩
  apply le_csInf (randomizedSet_nonempty cost)
  rintro z ⟨q, hq, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost hp hq

/-- The hard direction, via separation of the compact convex set of achievable cost vectors
from the closed convex set of vectors bounded by `c`: for every `c` strictly below the
randomized complexity there is an input distribution witnessing that the distributional
complexity is at least `c`. -/
