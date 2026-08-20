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

theorem yao_principle_iInf_iSup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    (⨅ p : {p : A → ℝ // IsDist p}, randCost c (p : A → ℝ))
      = ⨆ q : {q : I → ℝ // IsDist q}, distCost c (q : I → ℝ) := by
  have h1 : (⨅ p : {p : A → ℝ // IsDist p}, randCost c (p : A → ℝ)) = sInf (randCosts c) := by
    rw [randCosts, Set.image_eq_range]
    rfl
  have h2 : (⨆ q : {q : I → ℝ // IsDist q}, distCost c (q : I → ℝ)) = sSup (distCosts c) := by
    rw [distCosts, Set.image_eq_range]
    rfl
  rw [h1, h2, yao_principle]

end CS

