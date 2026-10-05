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

lemma dY_dY_sphereFactor (x y : ℝ) :
    dY (dY sphereFactor) (x, y) = (2 * y ^ 2 - 2 * x ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
  have hcd : ContDiff ℝ ∞ (dY sphereFactor) := contDiff_dY contDiff_sphereFactor
  have h1 : HasDerivAt (fun t : ℝ => dY sphereFactor (x, t))
      ((2 * y ^ 2 - 2 * x ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2) y := by
    rw [dY_sphereFactor]
    have hD : HasDerivAt (fun t : ℝ => 1 + x ^ 2 + t ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (1 + x ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have hnum : HasDerivAt (fun t : ℝ => -(2 * t)) (-2 : ℝ) y := by
      simpa using ((hasDerivAt_id y).const_mul (2 : ℝ)).neg
    have h := hnum.div hD hne
    simp only at h ⊢
    convert h using 1
    field_simp
    ring
  exact (h1.unique (hasDerivAt_dY hcd x y)).symm

