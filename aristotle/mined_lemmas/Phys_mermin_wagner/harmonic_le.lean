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


theorem harmonic_le (R : ℕ) : ∑ i ∈ Finset.range R, (1 : ℝ) / (i + 1) ≤ 1 + Real.log R := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  obtain ⟨M, rfl⟩ : ∃ M, R = M + 1 := ⟨R - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hstep : ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1 + 1)
      ≤ ∑ i ∈ Finset.range M, (Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := inv_le_log_diff i
    have e1 : ((i : ℝ) + 1 + 1) = ((i : ℝ) + 2) := by ring
    rw [e1]
    exact this
  have htel : ∑ i ∈ Finset.range M,
      (Real.log (((i : ℝ) + 1) + 1) - Real.log ((i : ℝ) + 1)) = Real.log ((M : ℝ) + 1) := by
    have := Finset.sum_range_sub (fun i : ℕ => Real.log ((i : ℝ) + 1)) M
    simpa using this
  have : ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1 + 1) ≤ Real.log ((M : ℝ) + 1) := by
    rw [← htel]; exact hstep
  push_cast
  have h01 : (1 : ℝ) / (0 + 1) = 1 := by norm_num
  rw [h01]
  linarith

/-! ### The spin-wave profile -/

/-- Radial profile of the spin wave: equal to `π` at the origin, vanishing at
`ℓ^∞`-distance `≥ R`, and logarithmically interpolating in between. -/
