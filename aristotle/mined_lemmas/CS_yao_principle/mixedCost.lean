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

def mixedCost (cost : A → X → ℝ) (q : A → ℝ) (x : X) : ℝ := ∑ a, q a * cost a x

/-- Expected cost of the deterministic algorithm `a` on an input drawn from the
distribution `p`. -/
