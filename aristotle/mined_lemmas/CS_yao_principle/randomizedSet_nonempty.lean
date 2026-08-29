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

lemma randomizedSet_nonempty [Nonempty A] [DecidableEq A] (cost : A → X → ℝ) :
    ((fun q => ⨆ x, mixedCost cost q x) '' stdSimplex ℝ A).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex A (Classical.arbitrary A))⟩

omit [Fintype A] in
