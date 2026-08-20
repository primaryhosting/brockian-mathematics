/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set Complex

namespace Math

/-- A continuous real function whose cosine is everywhere positive cannot decrease by `2π`
over an interval: the "winding" obstruction. -/

theorem re_conj_mul_sub_pos {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ z) :
    0 < ((starRingEnd ℂ) z * (z - w)).re := by
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => x ^ 2) hz
    simpa [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt,
      add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)] using this
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h0 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt
      (add_nonneg (sq_nonneg w.re) (sq_nonneg w.im))] at h0
    exact h0
  have key : ((starRingEnd ℂ) z * (z - w)).re
      = z.re * (z.re - w.re) + z.im * (z.im - w.im) := by
    simp [Complex.mul_re]
  rw [key]
  by_contra h
  push_neg at h
  have hre : w.re = z.re ∧ w.im = z.im := by
    constructor <;> nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  exact hne (Complex.ext hre.1 hre.2)

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
unit disk in `ℂ` (the closed 2-dimensional disk) has a fixed point. -/
