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

lemma integral_plane_inv_sq : ∫ p : ℝ × ℝ, (4:ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 = 4 * Real.pi := by
  rw [← integral_comp_polarCoord_symm (fun p : ℝ × ℝ => (4:ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2)]
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • ((4:ℝ) / (1 + (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) ^ 2)
        = (fun r : ℝ => 4 * r / (1 + r ^ 2) ^ 2) p.1 * (fun _ : ℝ => (1:ℝ)) p.2 := by
    intro p _
    have hs : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    rw [hs]
    have hsc : 1 + (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = 1 + p.1 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    simp only [hsc, smul_eq_mul, mul_one]
    ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, polarCoord_target,
    Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => 4 * r / (1 + r ^ 2) ^ 2) (fun _ : ℝ => (1:ℝ)) (Set.Ioi 0)
    (Set.Ioo (-Real.pi) Real.pi)
  rw [h, integral_Ioi_radial, setIntegral_const, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by nlinarith [Real.pi_pos]), smul_eq_mul]
  ring

/-- **Chern–Gauss–Bonnet for the round two-sphere.**  In stereographic coordinates the round
metric of `S²` is the conformal metric with factor `sphereFactor`, and its total curvature is
`2π · χ(S²) = 2π · 2 = 4π`. -/
