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


theorem swProfile_diff_le {d R : ℕ} (hR : 1 ≤ R) {x y : Fin d → ℤ} (hxy : adj x y) :
    |swProfile d R x - swProfile d R y|
      ≤ Real.pi / (((max (lnorm x) 1 : ℕ) : ℝ) * Real.log ((R : ℝ) + 1)) := by
  have hL : 0 < Real.log ((R : ℝ) + 1) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have h1 : lnorm y ≤ lnorm x + 1 := adj_lnorm_le hxy
  have h2 : lnorm x ≤ lnorm y + 1 := adj_lnorm_le (adj_symm hxy)
  rcases eq_or_lt_of_le (Nat.zero_le (lnorm x)) with h0 | h0
  · -- `lnorm x = 0`, so `max (lnorm x) 1 = 1`
    have hmax : (max (lnorm x) 1 : ℕ) = 1 := by omega
    rw [hmax]
    have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hcast, one_mul]
    have hx0 : lnorm x = 0 := by omega
    have hcases : lnorm y = 0 ∨ lnorm y = 1 := by omega
    rcases hcases with hy | hy
    · unfold swProfile
      rw [hx0, hy, sub_self, abs_zero]
      positivity
    · have hstep := prof_step R 0 hR
      simp only [Nat.cast_zero, zero_add, one_mul] at hstep
      unfold swProfile
      rw [hx0, hy]
      exact hstep
  · -- `lnorm x ≥ 1`
    have hmax : (max (lnorm x) 1 : ℕ) = lnorm x := by omega
    rw [hmax]
    rcases lt_trichotomy (lnorm y) (lnorm x) with hlt | heq | hgt
    · -- `lnorm y = lnorm x - 1`
      have hy : lnorm x = lnorm y + 1 := by omega
      have hstep := prof_step R (lnorm y) hR
      unfold swProfile
      rw [hy, abs_sub_comm]
      have hcast : ((lnorm y + 1 : ℕ) : ℝ) = ((lnorm y : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact hstep
    · unfold swProfile
      rw [heq]
      simp only [sub_self, abs_zero]
      positivity
    · -- `lnorm y = lnorm x + 1`
      have hy : lnorm y = lnorm x + 1 := by omega
      have hstep := prof_step R (lnorm x) hR
      unfold swProfile
      rw [hy]
      refine hstep.trans ?_
      have hpos : (0:ℝ) < ((lnorm x : ℕ) : ℝ) := by
        have : (1:ℝ) ≤ ((lnorm x : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
      have : ((lnorm x : ℕ) : ℝ) ≤ ((lnorm x : ℕ) : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right this hL.le

/-- Far from the origin the profile is identically zero, so the corresponding
gradient terms vanish. -/
