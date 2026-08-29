/- (Lean 4 requires `import` to be the first command, so this header is a plain block comment.)
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory

/-! ## Conformal metrics on the plane

We work with a smooth conformal factor `F : ℝ² → ℝ` and the Riemannian metric
`g = e^{2F} (dx² + dy²)`.  Its Gauss curvature is `K = -e^{-2F} Δ F` and its area element is
`e^{2F} dx dy`, so that the curvature density `K · e^{2F}` is exactly `-Δ F`.
-/

/-- Partial derivative in the `x`-direction of a function on the plane. -/

theorem chern_gauss_bonnet (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) :
    ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = 2 * Real.pi * (0 : ℝ) := by
  have hcontXX : Continuous (dX (dX F)) := (contDiff_dX (contDiff_dX hF)).continuous
  have hcontYY : Continuous (dY (dY F)) := (contDiff_dY (contDiff_dY hF)).continuous
  have inner : ∀ x : ℝ, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
    intro x
    have h1 : IntervalIntegrable (fun y : ℝ => -dX (dX F) (x, y)) volume 0 1 :=
      ((hcontXX.comp (by fun_prop)).neg).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun y : ℝ => -dY (dY F) (x, y)) volume 0 1 :=
      ((hcontYY.comp (by fun_prop)).neg).intervalIntegrable 0 1
    calc ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
        = ∫ y in (0:ℝ)..1, (-dX (dX F) (x, y) + -dY (dY F) (x, y)) := by
          simp only [gaussCurvature_mul_areaDensity]
      _ = (∫ y in (0:ℝ)..1, -dX (dX F) (x, y)) + ∫ y in (0:ℝ)..1, -dY (dY F) (x, y) :=
          intervalIntegral.integral_add h1 h2
      _ = ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
          have hzero : ∫ y in (0:ℝ)..1, -dY (dY F) (x, y) = 0 := by
            rw [intervalIntegral.integral_neg, integral_dY_dY_eq_zero hF hy x, neg_zero]
          rw [hzero, add_zero]
  calc ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
        simp only [inner]
    _ = ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, -dX (dX F) (x, y) :=
        swap_unit_square (fun p => -dX (dX F) p) hcontXX.neg
    _ = 2 * Real.pi * (0 : ℝ) := by
        have hzero : ∀ y : ℝ, ∫ x in (0:ℝ)..1, -dX (dX F) (x, y) = 0 := by
          intro y
          rw [intervalIntegral.integral_neg, integral_dX_dX_eq_zero hF hx y, neg_zero]
        simp [hzero]

/-! ## Sanity check: the round sphere

Stereographic projection identifies `S² ∖ {pt}` with `ℝ²`, and transports the round metric of the
unit sphere to the conformal metric `e^{2F}(dx²+dy²)` with `F = log 2 - log (1 + x² + y²)`.
We check that the definitions above indeed return Gauss curvature identically `1` for this
conformal factor, which is the defining property of the unit round sphere. -/

/-- The conformal factor of the round unit sphere in stereographic coordinates. -/
