import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig


theorem one_sub_cos_le_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h2 : Real.cos (2 * (x / 2)) = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    rw [show 2 * (x / 2) = x by ring] at h2; exact h2
  have h3 : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  nlinarith [sq_abs (Real.sin (x / 2)), sq_abs (x / 2), abs_nonneg (Real.sin (x / 2)),
    abs_nonneg (x / 2)]

