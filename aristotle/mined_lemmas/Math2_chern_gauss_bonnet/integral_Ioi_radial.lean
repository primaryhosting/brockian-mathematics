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

lemma integral_Ioi_radial : ∫ x in Set.Ioi (0:ℝ), 4 * x / (1 + x ^ 2) ^ 2 = 2 := by
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun r : ℝ => -2 / (1 + r ^ 2)) (4 * x / (1 + x ^ 2) ^ 2) x := by
    intro x _
    have hD : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (hasDerivAt_const x (-2 : ℝ)).div hD hne
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun r : ℝ => -2 / (1 + r ^ 2)) (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    exact Continuous.div continuous_const (by fun_prop) fun r => by positivity
  have hlim : Filter.Tendsto (fun r : ℝ => -2 / (1 + r ^ 2)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop (by norm_num))
  have hpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ 4 * x / (1 + x ^ 2) ^ 2 := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  norm_num

