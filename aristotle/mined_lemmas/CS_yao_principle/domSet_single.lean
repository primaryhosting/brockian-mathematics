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

lemma domSet_single (c : A → I → ℝ) (a : A) : (fun i => c a i) ∈ domSet c := by
  refine ⟨Pi.single a 1, isDist_single a, fun i => ?_⟩
  have h : ∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i = c a i := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  exact le_of_eq h

/-- The open lower box `{y | ∀ i, y i < t}`. -/
