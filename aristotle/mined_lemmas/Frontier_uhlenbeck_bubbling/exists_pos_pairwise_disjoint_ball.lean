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

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

/-- The *bubbling set* (concentration set) of a sequence of energy measures `mu n` at
concentration threshold `eps`: those points where, at every scale `r > 0`, at least `eps`
of the energy is asymptotically present. -/

private lemma exists_pos_pairwise_disjoint_ball {X : Type*} [MetricSpace X] (t : Finset X) :
    ∃ r : ℝ, 0 < r ∧
      (t : Set X).Pairwise (fun x y => Disjoint (Metric.ball x r) (Metric.ball y r)) := by
  rcases Set.subsingleton_or_nontrivial (t : Set X) with h | h
  · exact ⟨1, one_pos, h.pairwise _⟩
  · refine ⟨(t : Set X).infsep / 2, by
      have := (t.finite_toSet.infsep_pos_iff_nontrivial).2 h
      linarith, ?_⟩
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := Set.infsep_le_dist_of_mem hx hy hxy
    linarith

/-- Key quantitative step: any finite family of bubbling points carries `eps` of energy each,
inside pairwise disjoint balls, hence its cardinality times `eps` is bounded by the total
energy bound `E`. -/
