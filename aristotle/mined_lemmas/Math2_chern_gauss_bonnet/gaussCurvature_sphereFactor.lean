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

theorem gaussCurvature_sphereFactor (p : ℝ × ℝ) : gaussCurvature sphereFactor p = 1 := by
  have hexp : Real.exp (-(2 * sphereFactor p)) = (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 / 4 := by
    unfold sphereFactor
    rw [show -(2 * (Real.log 2 - Real.log (1 + p.1 ^ 2 + p.2 ^ 2)))
          = 2 * Real.log (1 + p.1 ^ 2 + p.2 ^ 2) - 2 * Real.log 2 by ring, Real.exp_sub,
      show (2:ℝ) * Real.log (1 + p.1 ^ 2 + p.2 ^ 2) = Real.log ((1 + p.1 ^ 2 + p.2 ^ 2) ^ 2) by
        rw [Real.log_pow]; push_cast; ring,
      show (2:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), Real.exp_log (by norm_num)]
    norm_num
  have hne : ((1 + p.1 ^ 2 + p.2 ^ 2) : ℝ) ^ 2 ≠ 0 := by positivity
  simp only [gaussCurvature, hexp, lapl_sphereFactor]
  field_simp

/-! ## Chern–Gauss–Bonnet for the round sphere

Stereographic coordinates cover `S²` up to a single point, a set of measure zero, so the total
curvature of the round sphere is computed by an integral over all of `ℝ²`.  It equals
`4π = 2π · χ(S²)`, the Chern–Gauss–Bonnet formula for the closed surface `S²`. -/

