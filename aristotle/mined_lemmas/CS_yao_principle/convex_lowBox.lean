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

lemma convex_lowBox (t : ℝ) : Convex ℝ (lowBox I t) := by
  intro y hy z hz s r hs hr hsr i
  rcases eq_or_lt_of_le hs with h | h
  · have hr1 : r = 1 := by linarith
    simpa [← h, hr1] using hz i
  · have : s * y i + r * z i < s * t + r * t := by
      have h1 : s * y i < s * t := by nlinarith [hy i]
      have h2 : r * z i ≤ r * t := by nlinarith [hz i]
      linarith
    simpa [Pi.add_apply, smul_eq_mul, ← add_mul, hsr] using this

/-- Linear functionals on `I → ℝ` are given by coefficient vectors. -/
