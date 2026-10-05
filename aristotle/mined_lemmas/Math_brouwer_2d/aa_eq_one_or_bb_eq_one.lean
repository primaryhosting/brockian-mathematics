import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Metric Set

namespace Brouwer2D

noncomputable section

/-- The punctured complex plane, the base of the exponential covering map. -/
abbrev Cstar := {z : ℂ // z ≠ 0}

/-- The exponential covering map `ℂ → ℂ \ {0}`. -/

theorem aa_eq_one_or_bb_eq_one (s : ℝ) : aa s = 1 ∨ bb s = 1 := by
  rcases le_or_gt s (1 / 2) with h | h
  · right
    have : (1 : ℝ) ≤ 2 - 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ 2 - 2 * s := by linarith
    rw [bb, max_eq_left h0, min_eq_right this]
  · left
    have h1 : (1 : ℝ) ≤ 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ 2 * s := by linarith
    rw [aa, max_eq_left h0, min_eq_right h1]

section Main

variable {f : ℂ → ℂ}

/-- The homotopy, as a map `ℝ × ℝ → ℂ`: it interpolates from the constant loop `-f 0`
(at `s = 0`) through the loop `z - f z` on the unit circle (at `s = 1/2`) to the loop
`z` (at `s = 1`). -/
