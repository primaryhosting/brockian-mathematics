/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
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

set_option grind.warning false

namespace Frontier

/-! ## The descent machinery

Mordell's theorem states that the group `E(ℚ)` of rational points of an elliptic curve over `ℚ`
is finitely generated.  Its classical proof has two inputs:

* the *weak Mordell–Weil theorem*: the quotient `E(ℚ)/2E(ℚ)` is finite;
* the *theory of heights*: there is a height function `h : E(ℚ) → ℝ` satisfying the three
  standard properties recorded in `Frontier.HeightData` below.

The purely group-theoretic step which combines these two inputs into finite generation is the
*descent theorem*, `Frontier.fg_of_quotient_two_finite_of_heightData`, which is proved here in
full generality for an arbitrary additive commutative group.  The target theorem
`Frontier.Mordell_finite_generation` is the resulting Lean-checked reduction of Mordell's

def intHeightData : HeightData ℤ where
  h n := (n : ℝ) ^ 2
  quasi_parallelogram Q := ⟨2 * (Q : ℝ) ^ 2, by
    intro P
    have : (0 : ℝ) ≤ ((P : ℝ) - (Q : ℝ)) ^ 2 := sq_nonneg _
    push_cast
    nlinarith⟩
  duplication := ⟨0, by
    intro P
    push_cast
    nlinarith [sq_nonneg ((P : ℝ))]⟩
  finite_of_bounded C := by
    apply Set.Finite.subset (Set.finite_Icc (-⌈max C 1⌉) ⌈max C 1⌉)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have h1 : |(n : ℝ)| ≤ max C 1 := by
      rcases le_or_gt |(n : ℝ)| 1 with h | h
      · exact le_trans h (le_max_right _ _)
      · have hsq : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
          nlinarith [sq_abs ((n : ℝ)), abs_nonneg ((n : ℝ))]
        exact le_trans hsq (le_trans hn (le_max_left _ _))
    have h2 : (|n| : ℝ) ≤ (⌈max C 1⌉ : ℝ) := le_trans (by simpa using h1) (Int.le_ceil _)
    have h3 : |n| ≤ ⌈max C 1⌉ := by exact_mod_cast h2
    have h4 := abs_le.mp h3
    simp only [Set.mem_Icc]
    omega

/-- The base case of the descent argument: applied to `ℤ` (with its `2`-descent data and its
height function), the descent theorem yields that `ℤ` is finitely generated. -/
