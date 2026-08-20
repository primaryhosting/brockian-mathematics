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

theorem zero_mem_bubbleSet_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : E4 → V) (eps : ℝ≥0∞) {R : ℝ} (hG : eps ≤ energyOn volume G (ball 0 R)) :
    (0 : E4) ∈ bubbleSet volume (fun n : ℕ => rescale ((n : ℝ) + 1) G) eps ∧
      ∀ n : ℕ, energyOn volume (rescale ((n : ℝ) + 1) G) Set.univ
        = energyOn volume G Set.univ := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  constructor
  · intro r hr
    obtain ⟨N, hN⟩ := exists_nat_gt (R / r)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hball : ((n : ℝ) + 1) • (ball (0 : E4) r) = ball 0 (((n : ℝ) + 1) * r) := by
      rw [smul_ball (ne_of_gt (hpos n)) (0 : E4) r]
      simp [Real.norm_eq_abs, abs_of_nonneg (hpos n).le]
    have hRle : R ≤ ((n : ℝ) + 1) * r := by
      have hNr : R / r < (N : ℝ) := hN
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : R / r < (n : ℝ) + 1 := by linarith
      calc R = R / r * r := by field_simp
        _ ≤ ((n : ℝ) + 1) * r := by nlinarith
    calc eps ≤ energyOn volume G (ball 0 R) := hG
      _ ≤ energyOn volume G (ball 0 (((n : ℝ) + 1) * r)) :=
          energyOn_mono _ _ (Metric.ball_subset_ball hRle)
      _ = energyOn volume (rescale ((n : ℝ) + 1) G) (ball 0 r) := by
          rw [energyOn_rescale G (hpos n) measurableSet_ball, hball]
  · intro n
    rw [energyOn_rescale G (hpos n) MeasurableSet.univ,
      smul_set_univ₀ (ne_of_gt (hpos n))]

end Rescaling

/-! ## Removable singularities -/

/-- **Removable singularity for the energy.**  A puncture carries no Yang–Mills energy: the energy
of a field on a punctured region equals its energy on the whole region.  This is the measure
theoretic half of the removable singularity theorem, and shows that the finite-energy condition
on `s \ {c}` is the same as on `s`. -/
