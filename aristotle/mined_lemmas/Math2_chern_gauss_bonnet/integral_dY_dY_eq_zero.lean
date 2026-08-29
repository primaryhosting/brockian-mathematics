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

lemma integral_dY_dY_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) (x : ℝ) :
    ∫ y in (0:ℝ)..1, dY (dY F) (x, y) = 0 := by
  have hcont : Continuous fun y : ℝ => dY (dY F) (x, y) :=
    (contDiff_dY (contDiff_dY hF)).continuous.comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => dY F (x, t)) (f' := fun t => dY (dY F) (x, t)) (a := 0) (b := 1)
    (fun t _ => hasDerivAt_dY (contDiff_dY hF) x t) (hcont.intervalIntegrable 0 1)
  rw [h]
  have hp := dY_periodic hF hy x 0
  rw [zero_add] at hp
  simp [hp]

/-- The curvature density of the conformal metric is minus the flat Laplacian of `F`. -/
