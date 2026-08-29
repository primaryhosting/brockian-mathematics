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

theorem chern_gauss_bonnet_sphere :
    ∫ p : ℝ × ℝ, gaussCurvature sphereFactor p * areaDensity sphereFactor p
      = 2 * Real.pi * 2 := by
  have hint : ∀ p : ℝ × ℝ, gaussCurvature sphereFactor p * areaDensity sphereFactor p
      = 4 / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 := by
    intro p
    have h1 := gaussCurvature_mul_areaDensity sphereFactor p
    have h2 := lapl_sphereFactor p
    simp only [lapl] at h2
    rw [show (-4 : ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2
      = -(4 / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2) by ring] at h2
    rw [h1]
    linarith
  simp only [hint]
  rw [integral_plane_inv_sq]
  ring

end Math2

