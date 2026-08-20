/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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

namespace Frontier

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

theorem energyOn_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : E4 → V)
    {lam : ℝ} (hlam : 0 < lam) {s : Set E4} (hs : MeasurableSet s) :
    energyOn volume (rescale lam F) s = energyOn volume F (lam • s) := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hrank : Module.finrank ℝ E4 = 4 := by
    simp [E4]
  have hnorm : ∀ x : E4, ((‖rescale lam F x‖₊ : ℝ≥0∞) ^ 2)
      = ENNReal.ofReal (lam ^ 4) * ((‖F (lam • x)‖₊ : ℝ≥0∞) ^ 2) := by
    intro x
    have h1 : ‖rescale lam F x‖₊ = ‖(lam ^ 2 : ℝ)‖₊ * ‖F (lam • x)‖₊ := by
      simp only [rescale, nnnorm_smul]
    rw [h1]
    push_cast
    rw [mul_pow]
    congr 1
    have h2 : ((‖(lam ^ 2 : ℝ)‖₊ : ℝ≥0∞)) = ENNReal.ofReal (lam ^ 2) := by
      simp [ENNReal.ofReal, Real.nnnorm_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ 2),
        Real.toNNReal_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ 2)]
    rw [h2, ← ENNReal.ofReal_pow (by positivity)]
    ring_nf
  unfold energyOn
  simp only [hnorm]
  rw [lintegral_const_mul' _ _ (by simp),
    setLIntegral_comp_smul volume (fun y => ((‖F y‖₊ : ℝ≥0∞)) ^ 2) hlam0 hs, hrank,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (lam ^ 4)⁻¹), mul_inv_cancel₀ (by positivity)]
  simp

/-- **Bubbles do occur.**  The statement of `uhlenbeck_bubbling` is not vacuous: given any
Yang–Mills field `G` on `ℝ⁴` carrying at least `eps` of energy on some ball around the origin,
the conformally rescaled sequence `F n = rescale (n+1) G` has the origin in its bubbling set,
while every member of the sequence has exactly the same total energy as `G`.  This is the
standard bubbling construction. -/
