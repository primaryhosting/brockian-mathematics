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

lemma distCosts_bddAbove (c : A → I → ℝ) [Nonempty A] [Nonempty I] :
    BddAbove (distCosts c) := by
  refine ⟨randCost c (Pi.single (Classical.arbitrary A) 1), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact distCost_le_randCost c (isDist_single _) hq

/-- The "upper" set of cost vectors dominated by some randomized algorithm. -/
