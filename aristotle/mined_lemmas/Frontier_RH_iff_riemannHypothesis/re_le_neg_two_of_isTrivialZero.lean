import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
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

open Complex

/-- A *trivial zero* of the Riemann zeta function is one of the points `-2, -4, -6, …`. -/

theorem re_le_neg_two_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) : s.re ≤ -2 := by
  obtain ⟨n, rfl⟩ := hs
  have : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Reflection.** If `s` is a nontrivial zero, so is `1 - s`. -/
