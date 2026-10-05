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

lemma integral_dX_dX_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p) (y : ℝ) :
    ∫ x in (0:ℝ)..1, dX (dX F) (x, y) = 0 := by
  have hcont : Continuous fun x : ℝ => dX (dX F) (x, y) :=
    (contDiff_dX (contDiff_dX hF)).continuous.comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => dX F (s, y)) (f' := fun s => dX (dX F) (s, y)) (a := 0) (b := 1)
    (fun s _ => hasDerivAt_dX (contDiff_dX hF) s y) (hcont.intervalIntegrable 0 1)
  rw [h]
  have hp := dX_periodic hF hx 0 y
  rw [zero_add] at hp
  simp [hp]

/-- The integral of `∂²F/∂y²` over a period in `y` vanishes. -/
