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

def avgCost (cost : A → X → ℝ) (p : X → ℝ) (a : A) : ℝ := ∑ x, p x * cost a x

/-- The randomized complexity: the least, over randomized algorithms (distributions `q`
over deterministic algorithms), of the worst-case expected cost. -/
