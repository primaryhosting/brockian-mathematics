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

lemma gaussCurvature_mul_areaDensity (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    gaussCurvature F p * areaDensity F p = -dX (dX F) p + -dY (dY F) p := by
  have hexp : Real.exp (-(2 * F p)) * Real.exp (2 * F p) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [gaussCurvature, areaDensity, lapl]
  calc -Real.exp (-(2 * F p)) * (dX (dX F) p + dY (dY F) p) * Real.exp (2 * F p)
      = -((dX (dX F) p + dY (dY F) p) *
          (Real.exp (-(2 * F p)) * Real.exp (2 * F p))) := by ring
    _ = -dX (dX F) p + -dY (dY F) p := by rw [hexp]; ring

/-! ## The theorem -/

/-- **Chern–Gauss–Bonnet on the two-dimensional torus** `T² = ℝ²/ℤ²`.

Let `F : ℝ² → ℝ` be smooth and doubly periodic with period lattice `ℤ²`; equivalently, `F` is a
smooth function on the torus `T²`.  It defines the Riemannian metric `g = e^{2F}(dx² + dy²)` on
`T²`, whose Gauss curvature is `K = -e^{-2F} Δ F` and whose Riemannian area element is
`e^{2F} dx dy`.  The theorem states that the total curvature of `g`, integrated over the
fundamental domain `[0,1]²`, equals `2π · χ(T²)`, where the Euler characteristic of the
two-torus is `χ(T²) = 0`.

In dimension two the Chern–Gauss–Bonnet integrand (the Pfaffian of the curvature form divided
by `(2π)^n`) is exactly `K / (2π)` times the area form, so this is the Chern–Gauss–Bonnet
formula for the closed even-dimensional manifold `T²` equipped with an arbitrary conformal
metric. -/
