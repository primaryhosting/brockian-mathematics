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

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

lemma re_sub_mul_conj_pos {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ z) :
    0 < ((z - w) * (starRingEnd ℂ) z).re := by
  set a : ℂ := w * (starRingEnd ℂ) z with ha
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hre : ((z - w) * (starRingEnd ℂ) z).re = 1 - a.re := by
    rw [sub_mul, hzz]; simp [ha]
  rw [hre, sub_pos]
  by_contra h
  push_neg at h
  have hna : ‖a‖ ≤ 1 := by
    rw [ha, norm_mul, RCLike.norm_conj, hz, mul_one]; exact hw
  have h1 : a.re ≤ ‖a‖ := Complex.re_le_norm a
  have hre1 : a.re = 1 := le_antisymm (le_trans h1 hna) h
  have hn1 : ‖a‖ = 1 := le_antisymm hna (by rw [← hre1]; exact h1)
  have him : a.im = 0 := by
    have h2 := Complex.normSq_eq_norm_sq a
    rw [hn1, Complex.normSq_apply, hre1] at h2
    nlinarith [sq_nonneg a.im]
  have haa : a = 1 := by
    apply Complex.ext <;> simp [hre1, him]
  refine hne ?_
  have := congrArg (· * z) haa
  simp only [one_mul] at this
  rw [ha, mul_assoc, mul_comm ((starRingEnd ℂ) z) z, hzz, mul_one] at this
  exact this

/-! ### Brouwer's fixed point theorem in the complex plane -/

