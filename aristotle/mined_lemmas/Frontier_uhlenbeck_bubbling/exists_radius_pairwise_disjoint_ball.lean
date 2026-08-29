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

open Filter MeasureTheory Metric

/-! ## Auxiliary lemmas -/

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem exists_radius_pairwise_disjoint_ball {X : Type*} [MetricSpace X] {s : Set X}
    (hs : s.Finite) :
    ∃ r > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (ball x r) (ball y r) := by
  obtain ⟨C, hC, hC2⟩ := hs.relatively_discrete
  set c : ENNReal := min C 1 with hc
  have hcpos : 0 < c := lt_min hC (by norm_num)
  have hcne : c ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hcpos.ne' hcne
  refine ⟨c.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have h1 : c ≤ edist x y := le_trans (min_le_left _ _) (hC2 x hx y hy hxy)
  have h2 : c.toReal ≤ (edist x y).toReal := ENNReal.toReal_mono (edist_ne_top x y) h1
  rw [← dist_edist] at h2
  linarith

/-- **Energy count at concentration points.** If each measure `μ n` has total mass at most `E`
and `t` is a finite set of points at which the energy persistently concentrates with quantum `ε`
(i.e. every ball around such a point carries asymptotic mass at least `ε`), then
`(#t) * ε ≤ E`. -/
