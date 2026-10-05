import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/

theorem gauss_bonnet_conformal_torus (hu : IsPotential u) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
      = 2 * Real.pi * (torusEulerChar : ℝ) := by
  have hpt : ∀ x y : ℝ, gaussCurvature u x y * areaDensity u x y
      = -(px (px u) x y) - py (py u) x y := by
    intro x y
    have h : Real.exp (-(2 * u x y)) * Real.exp (2 * u x y) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [gaussCurvature, areaDensity]
    linear_combination (-(px (px u) x y + py (py u) x y)) * h
  have hinner : ∀ x : ℝ,
      (∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
        = ∫ y in (0 : ℝ)..1, -(px (px u) x y) := by
    intro x
    have hc1 : Continuous fun t => -(px (px u) x t) :=
      (hu.cont_fst_fst.comp (continuous_const.prodMk continuous_id)).neg
    have hc2 : Continuous fun t => py (py u) x t :=
      hu.cont_snd_snd.comp (continuous_const.prodMk continuous_id)
    calc (∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
        = ∫ y in (0 : ℝ)..1, (-(px (px u) x y) + -(py (py u) x y)) := by
          refine intervalIntegral.integral_congr ?_
          intro y _
          show gaussCurvature u x y * areaDensity u x y
            = -(px (px u) x y) + -(py (py u) x y)
          rw [hpt x y]; ring
      _ = (∫ y in (0 : ℝ)..1, -(px (px u) x y)) + ∫ y in (0 : ℝ)..1, -(py (py u) x y) :=
          intervalIntegral.integral_add (hc1.intervalIntegrable 0 1)
            (hc2.neg.intervalIntegrable 0 1)
      _ = ∫ y in (0 : ℝ)..1, -(px (px u) x y) := by
          have hzero : (∫ y in (0 : ℝ)..1, -(py (py u) x y)) = 0 := by
            rw [intervalIntegral.integral_neg, hu.integral_pyy x, neg_zero]
          rw [hzero, add_zero]
  rw [intervalIntegral.integral_congr (fun x _ => hinner x)]
  simp only [intervalIntegral.integral_neg]
  rw [hu.integral_integral_pxx]
  simp [torusEulerChar]

/-! ## The hypotheses are satisfiable -/

/-- A constant potential (a flat metric on the torus) satisfies the hypotheses. -/
