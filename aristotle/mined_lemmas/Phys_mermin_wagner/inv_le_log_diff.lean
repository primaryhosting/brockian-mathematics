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


theorem inv_le_log_diff (i : ℕ) : (1 : ℝ) / (i + 2) ≤ Real.log (i + 2) - Real.log (i + 1) := by
  have h1 : (0:ℝ) < ((i : ℝ) + 1) / ((i : ℝ) + 2) := by positivity
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : ((i:ℝ) + 1) / ((i:ℝ) + 2) - 1 = -(1 / ((i:ℝ) + 2)) := by field_simp; ring
  rw [h2] at h
  linarith

