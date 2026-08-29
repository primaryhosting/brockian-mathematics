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

lemma distributionalSet_bddAbove [Nonempty A] [Nonempty X] [DecidableEq A] (cost : A → X → ℝ) :
    BddAbove ((fun p => ⨅ a, avgCost cost p a) '' stdSimplex ℝ X) := by
  refine ⟨⨆ x, mixedCost cost (Pi.single (Classical.arbitrary A) 1) x, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost hp (single_mem_stdSimplex A _)

