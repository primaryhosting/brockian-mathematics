/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Metric Complex

namespace Math

noncomputable section

/-- If `x` lies on the unit circle, `w` lies in the closed unit disk and `w ≠ x`, then the
vector `x - w` makes an acute angle with `x`. -/

lemma re_sub_mul_conj_pos {x w : ℂ} (hx : ‖x‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ x) :
    0 < ((x - w) * (starRingEnd ℂ) x).re := by
  have hx' : x.re ^ 2 + x.im ^ 2 = 1 := by
    have h := Complex.sq_norm x
    rw [hx] at h
    simpa [Complex.normSq_apply, sq] using h.symm
  have hw' : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h1 := Complex.sq_norm w
    have h2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [h1] at h2
    simpa [Complex.normSq_apply, sq] using h2
  have hne' : 0 < (x.re - w.re) ^ 2 + (x.im - w.im) ^ 2 := by
    have hxw : x - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : 0 < ‖x - w‖ ^ 2 := by positivity
    rw [Complex.sq_norm] at h1
    simpa [Complex.normSq_apply, sq] using h1
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
unit disk in `ℂ ≃ ℝ²` has a fixed point. -/
