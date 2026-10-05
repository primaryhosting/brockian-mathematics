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

theorem ww_ne_zero (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1))
    (hfix : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≠ z) (s t : ℝ) :
    ww f s t ≠ 0 := by
  rcases eq_or_lt_of_le (bb_le_one s) with hb | hb
  · -- `bb s = 1`: the value is `z - f z` with `z` in the disk
    rw [ww, hb]
    intro hcon
    have : f ((aa s : ℂ) * ee t) = (aa s : ℂ) * ee t := by
      have := sub_eq_zero.mp (by simpa using hcon)
      linear_combination -this
    exact hfix _ (arg_mem_ball s t) this
  · -- `bb s < 1`, hence `aa s = 1`
    have ha : aa s = 1 := by
      rcases aa_eq_one_or_bb_eq_one s with h | h
      · exact h
      · exact absurd h (ne_of_lt hb)
    have hnf : ‖f ((aa s : ℂ) * ee t)‖ ≤ 1 := by
      have := hmaps (arg_mem_ball s t)
      simpa [mem_closedBall, dist_eq_norm] using this
    intro hcon
    have h0 : (aa s : ℂ) * ee t = (bb s : ℂ) * f ((aa s : ℂ) * ee t) := by
      have := sub_eq_zero.mp hcon
      exact this
    have h1 : ‖(aa s : ℂ) * ee t‖ = 1 := by
      rw [norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs, mul_one, ha, abs_one]
    have h2 : ‖(bb s : ℂ) * f ((aa s : ℂ) * ee t)‖ ≤ bb s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bb_nonneg s)]
      nlinarith [bb_nonneg s, norm_nonneg (f ((aa s : ℂ) * ee t))]
    rw [h0] at h1
    linarith [h1 ▸ h2]

