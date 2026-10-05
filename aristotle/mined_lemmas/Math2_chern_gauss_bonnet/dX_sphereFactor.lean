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

lemma dX_sphereFactor : dX sphereFactor = fun p => -(2 * p.1) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  funext p
  obtain ⟨x, y⟩ := p
  have h1 : HasDerivAt (fun s : ℝ => sphereFactor (s, y)) (-(2 * x) / (1 + x ^ 2 + y ^ 2)) x := by
    have hD : HasDerivAt (fun s : ℝ => 1 + s ^ 2 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (1 : ℝ)).add_const (y ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have h := (hD.log hne).const_sub (Real.log 2)
    convert h using 1
    field_simp
  exact (h1.unique (hasDerivAt_dX contDiff_sphereFactor x y)).symm

