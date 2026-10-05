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

lemma dY_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) (x y : ℝ) :
    dY F (x, y + 1) = dY F (x, y) := by
  have h1 : HasDerivAt (fun t => F (x, t)) (dY F (x, y + 1)) (y + 1) := hasDerivAt_dY hF x (y + 1)
  have h2 : HasDerivAt (fun t => F (x, t + 1)) (dY F (x, y + 1)) y := by
    simpa using h1.comp y ((hasDerivAt_id y).add_const 1)
  have h3 : (fun t => F (x, t + 1)) = fun t => F (x, t) := by
    funext t; exact hy (x, t)
  rw [h3] at h2
  exact h2.unique (hasDerivAt_dY hF x y)

/-! ## Integration over a fundamental domain -/

/-- Fubini's theorem for a continuous function on the unit square. -/
