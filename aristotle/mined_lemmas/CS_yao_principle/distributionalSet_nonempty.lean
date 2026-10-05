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

lemma distributionalSet_nonempty [Nonempty X] [DecidableEq X] (cost : A → X → ℝ) :
    ((fun p => ⨅ a, avgCost cost p a) '' stdSimplex ℝ X).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex X (Classical.arbitrary X))⟩

