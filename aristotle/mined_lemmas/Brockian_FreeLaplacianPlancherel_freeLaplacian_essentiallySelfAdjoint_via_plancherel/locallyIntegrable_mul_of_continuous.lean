import Mathlib

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

/-
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped ComplexInnerProductSpace

namespace Brockian.FreeLaplacianPlancherel

/-! ## Abstract theory of graphs of unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph of the adjoint of the (not necessarily bounded) operator whose graph is `G`:
the set of pairs `(g, h)` with `⟪T f, g⟫ = ⟪f, h⟫` for all `(f, T f) ∈ G`. -/

lemma locallyIntegrable_mul_of_continuous {g : ℝ → ℂ} (hg : Continuous g) {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun x => g x * f x) volume := by
  intro x
  obtain ⟨u, hu, hfu⟩ := hf x
  obtain ⟨V, hVu, hVopen, hxV⟩ := mem_nhds_iff.1 hu
  have hWopen : IsOpen (V ∩ Metric.ball x 1) := hVopen.inter Metric.isOpen_ball
  refine ⟨V ∩ Metric.ball x 1, hWopen.mem_nhds ⟨hxV, Metric.mem_ball_self one_pos⟩, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hg.continuousOn
  refine (hfu.mono_set (fun y hy => hVu hy.1)).bdd_mul (c := C)
    hg.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
  exact hC y (Metric.ball_subset_closedBall hy.2)

