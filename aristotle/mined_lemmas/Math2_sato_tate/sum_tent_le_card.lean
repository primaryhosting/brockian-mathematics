/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

lemma sum_tent_le_card {theta : ℕ → ℝ} {a b delta : ℝ} (hd : 0 < delta) (N : ℕ) :
    (∑ p ∈ primesBelow N, tent a b delta (theta p))
      ≤ (((primesBelow N).filter (fun p => theta p ∈ Set.Icc a b)).card : ℝ) := by
  classical
  rw [← Finset.sum_boole (fun p => theta p ∈ Set.Icc a b) (primesBelow N)]
  refine Finset.sum_le_sum ?_
  intro p _
  by_cases hp : theta p ∈ Set.Icc a b
  · rw [if_pos hp]; exact tent_le_one _ _ _ _
  · rw [if_neg hp]
    simp only [Set.mem_Icc, not_and_or, not_le] at hp
    rcases hp with h1 | h1
    · exact le_of_eq (tent_eq_zero_left hd h1.le)
    · exact le_of_eq (tent_eq_zero_right hd h1.le)

