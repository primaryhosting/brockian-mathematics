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

lemma swap_unit_square (G : ℝ × ℝ → ℝ) (hG : Continuous G) :
    ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, G (x, y) =
      ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, G (x, y) := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  simp only [intervalIntegral.integral_of_le h01]
  have hint : Integrable (Function.uncurry fun (x : ℝ) (y : ℝ) => G (x, y))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : IntegrableOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume) :=
      hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hc.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- The integral of `∂²F/∂x²` over a period in `x` vanishes. -/
