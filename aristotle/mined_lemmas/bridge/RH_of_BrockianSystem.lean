import Mathlib

/-!
# A formally audited Hilbert–Pólya conditional

This file separates two issues which the original draft conflated.

* `completedRiemannZeta₀` is Mathlib's *additively regularized* completed zeta
  function.  It is not the classical Riemann ξ-function, and its zeros are not
  the nontrivial zeros of `riemannZeta`.
* Symmetry of an unbounded operator, by itself, does not connect an arbitrary
  function called a determinant to a real spectrum.  That connection has to be
  an explicit hypothesis until a genuine spectral and determinant theory is
  supplied.

Accordingly, the corrected theorem below uses the classical entire factor
`riemannXi s = s (s - 1) completedRiemannZeta s`.  Its harmless conventional
constant factor `1/2` is omitted because it has no effect on zeros.  The
Brockian data explicitly includes the load-bearing conclusion that a zero of
its determinant has real spectral parameter.
-/

noncomputable section
open Complex
open scoped InnerProductSpace

/-- The set used in the submitted draft.  It is retained for auditability, but
it is not the set of nontrivial zeta zeros: Mathlib's `completedRiemannZeta₀`
is an additive pole-removal regularization, not the classical ξ-function. -/

theorem RH_of_BrockianSystem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : BrockianSystem H) : RiemannHypothesis := by
  apply bridge
  intro s ⟨hz, htriv, hs1⟩
  -- Define t = -I * (s - 1/2), so 1/2 + I*t = s
  let t : ℂ := -I * (s - 1/2)
  have ht : 1/2 + I * t = s := by
    simp [t]
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  -- Since s is a nontrivial zeta zero, riemannXi s = 0
  have hxi : riemannXi s = 0 := riemannXi_eq_zero_of_nontrivial_zeta_zero hz htriv hs1
  -- Rewrite using ht
  rw [← ht] at hxi
  -- By det_zero_iff_xi_zero, det.detFn t = 0
  have hdet : S.det.detFn t = 0 := (S.det_zero_iff_xi_zero t).mpr hxi
  -- By det_zero_im_zero, t.im = 0
  have him : t.im = 0 := S.det_zero_im_zero t hdet
  -- t = -I * (s - 1/2), so t.im = 1/2 - s.re
  have him_calc : t.im = 1/2 - s.re := by simp [t]
  linarith

end

