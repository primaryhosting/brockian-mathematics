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

lemma dX_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p) (x y : ℝ) :
    dX F (x + 1, y) = dX F (x, y) := by
  have h1 : HasDerivAt (fun s => F (s, y)) (dX F (x + 1, y)) (x + 1) := hasDerivAt_dX hF (x + 1) y
  have h2 : HasDerivAt (fun s => F (s + 1, y)) (dX F (x + 1, y)) x := by
    simpa using h1.comp x ((hasDerivAt_id x).add_const 1)
  have h3 : (fun s => F (s + 1, y)) = fun s => F (s, y) := by
    funext s; exact hx (s, y)
  rw [h3] at h2
  exact h2.unique (hasDerivAt_dX hF x y)

/-- If `F` is `1`-periodic in `y`, so is its `y`-partial derivative. -/
