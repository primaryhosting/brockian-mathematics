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

lemma randomizedSet_bddBelow [Nonempty A] [Nonempty X] [DecidableEq X] (cost : A → X → ℝ) :
    BddBelow ((fun q => ⨆ x, mixedCost cost q x) '' stdSimplex ℝ A) := by
  refine ⟨⨅ a, avgCost cost (Pi.single (Classical.arbitrary X) 1) a, ?_⟩
  rintro y ⟨q, hq, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost (single_mem_stdSimplex X _) hq

