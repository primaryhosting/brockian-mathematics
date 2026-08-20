/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A probability distribution on a finite type. -/

lemma weighted_le_ciSup [Nonempty α] {p : α → ℝ} (hp : IsDist p) (X : α → ℝ) :
    ∑ a, p a * X a ≤ ⨆ a, X a := by
  have hb : BddAbove (Set.range X) := Finite.bddAbove_range X
  calc ∑ a, p a * X a ≤ ∑ a, p a * (⨆ a', X a') := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (le_ciSup hb a) (hp.1 a)
    _ = ⨆ a, X a := by rw [← Finset.sum_mul, hp.2, one_mul]

end Aux

omit [DecidableEq A] [DecidableEq I] in
/-- **Easy direction of Yao's principle**: the distributional complexity of any input
distribution is a lower bound on the cost of any randomized algorithm. -/
