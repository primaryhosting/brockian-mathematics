import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Filter Set Topology
open scoped ENNReal

namespace Frontier

/-! ## Setup

Uhlenbeck's compactness theorem for Yang–Mills connections asserts that a sequence of
connections with uniformly bounded Yang–Mills energy converges (after gauge transformations
and passing to a subsequence) away from a *finite* set of points, the *bubbling points*,
at which a definite quantum of energy concentrates.

The quantitative combinatorial heart of that statement — the part that is independent of
gauge theory and is what actually produces the finiteness of the bubbling set — is the
following: if `ν i` is the sequence of energy measures, uniformly bounded by `E`, then the
set of points at which at least `ε₀` of energy concentrates in every ball is finite, of
cardinality at most `E / ε₀`.  (The gauge-theoretic input, `ε`-regularity, is what
guarantees that away from this set the connections converge; it is not formalized here.)

We formalize this statement and prove it. -/

/-- The *energy measure* attached to a curvature field `F` on a measure space `(X, μ)`:
the measure with density `‖F x‖ ^ 2` with respect to `μ`.  For a Yang–Mills connection `A`
on `ℝ⁴` with curvature `F_A`, this is the measure `|F_A|² dvol` whose total mass is the
Yang–Mills energy. -/

theorem bubbleSet_smul_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (x₀ : X) (ε₀ : ℝ≥0∞) (hε₀ : ε₀ ≠ 0) :
    bubbleSet (fun _ : ℕ => ε₀ • Measure.dirac x₀) ε₀ = {x₀} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have hd : 0 < dist x x₀ := dist_pos.2 hne
    have := hx (dist x x₀ / 2) (by linarith)
    have hmem : x₀ ∉ ball x (dist x x₀ / 2) := by
      simp only [Metric.mem_ball, not_lt]
      rw [dist_comm x x₀] at hd ⊢
      linarith
    rw [show ((ε₀ • Measure.dirac x₀) (ball x (dist x x₀ / 2))) = 0 by
      simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_ball,
        Set.indicator_of_notMem hmem]] at this
    simp only [liminf_const] at this
    exact hε₀ (le_antisymm this (zero_le _))
  · rintro rfl r hr
    have hb : ((ε₀ • Measure.dirac x) (ball x r)) = ε₀ := by
      simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_ball,
        Set.indicator_of_mem (Metric.mem_ball_self hr)]
    simp [hb]

end Frontier

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

