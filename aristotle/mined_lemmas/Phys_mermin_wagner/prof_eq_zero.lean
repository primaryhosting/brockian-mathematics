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


theorem prof_eq_zero {R k : ℕ} (hR : 1 ≤ R) (hk : R ≤ k) : prof R k = 0 := by
  have hL : Real.log ((R : ℝ) + 1) > 0 := by
    apply Real.log_pos; have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hle : Real.log ((R : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have : (R:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have : 1 - Real.log ((k : ℝ) + 1) / Real.log ((R : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hL]; linarith
  simp [prof, max_eq_left this]

