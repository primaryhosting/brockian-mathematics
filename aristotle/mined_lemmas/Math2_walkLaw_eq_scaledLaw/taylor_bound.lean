import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem taylor_bound (h : IsC3Test f f1 f2 f3 M) (w u : ℝ) :
    |f (w + u) - f w - f1 w * u - f2 w * u ^ 2 / 2| ≤ M * |u| ^ 3 := by
  have hM := h.nonneg
  set R : ℝ → ℝ := fun v => f (w + v) - f w - f1 w * v - f2 w * v ^ 2 / 2 with hRdef
  set R1 : ℝ → ℝ := fun v => f1 (w + v) - f1 w - f2 w * v with hR1def
  set R2 : ℝ → ℝ := fun v => f2 (w + v) - f2 w with hR2def
  -- derivatives
  have hdR : ∀ v, HasDerivAt R (R1 v) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => f (w + v)) (f1 (w + v)) v := by
      simpa using (h.hasDeriv0 (w + v)).comp v ((hasDerivAt_id v).const_add w)
    have h2 : HasDerivAt (fun v : ℝ => f1 w * v) (f1 w) v := by
      simpa using (hasDerivAt_id v).const_mul (f1 w)
    have h3 : HasDerivAt (fun v : ℝ => f2 w * v ^ 2 / 2) (f2 w * v) v := by
      have hh := ((hasDerivAt_pow 2 v).const_mul (f2 w)).div_const 2
      convert hh using 1
      ring
    exact ((h1.sub_const (f w)).sub h2).sub h3
  have hdR1 : ∀ v, HasDerivAt R1 (R2 v) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => f1 (w + v)) (f2 (w + v)) v := by
      simpa using (h.hasDeriv1 (w + v)).comp v ((hasDerivAt_id v).const_add w)
    have h2 : HasDerivAt (fun v : ℝ => f2 w * v) (f2 w) v := by
      simpa using (hasDerivAt_id v).const_mul (f2 w)
    exact (h1.sub_const (f1 w)).sub h2
  -- bounds
  have hb2 : ∀ v, |R2 v| ≤ M * |v| := by
    intro v
    have := h.lipschitz_f2 w (w + v)
    simpa [hR2def] using this
  have hb1 : ∀ v, |R1 v| ≤ M * |v| ^ 2 := by
    intro v
    have hzero : R1 0 = 0 := by simp [hR1def]
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := R1) (f' := R2)
      (s := Set.uIcc (0 : ℝ) v) (C := M * |v|)
      (fun z _ => (hdR1 z).hasDerivWithinAt)
      (fun z hz => by
        refine le_trans (by simpa [Real.norm_eq_abs] using hb2 z) ?_
        exact mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_uIcc hz) hM)
      (convex_uIcc _ _) (left_mem_uIcc) (right_mem_uIcc)
    rw [hzero] at this
    simpa [Real.norm_eq_abs, sq, mul_assoc] using this
  have hzero : R 0 = 0 := by simp [hRdef]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := R) (f' := R1)
    (s := Set.uIcc (0 : ℝ) u) (C := M * |u| ^ 2)
    (fun z _ => (hdR z).hasDerivWithinAt)
    (fun z hz => by
      refine le_trans (by simpa [Real.norm_eq_abs] using hb1 z) ?_
      have : z ^ 2 ≤ |u| ^ 2 := by
        have h0 : (0:ℝ) ≤ |z| := abs_nonneg _
        have hz2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
        nlinarith [abs_le_abs_of_mem_uIcc hz, abs_nonneg u]
      exact mul_le_mul_of_nonneg_left this hM)
    (convex_uIcc _ _) (left_mem_uIcc) (right_mem_uIcc)
  rw [hzero] at this
  have huR : |R u| ≤ M * |u| ^ 2 * |u| := by
    simpa [Real.norm_eq_abs] using this
  calc |f (w + u) - f w - f1 w * u - f2 w * u ^ 2 / 2| = |R u| := by rw [hRdef]
    _ ≤ M * |u| ^ 2 * |u| := huR
    _ = M * |u| ^ 3 := by ring

end IsC3Test

end Math2

import RequestProject.Taylor
import RequestProject.ConvPow

/-!
# The Lindeberg swapping argument

We compare the integral of a smooth test function against convolution powers of two probability
measures which have the same first two moments.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

section Moments

variable {P : Measure ℝ} [IsProbabilityMeasure P]

