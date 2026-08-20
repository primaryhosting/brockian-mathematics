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

theorem mem_bubbleSet_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X] (x : X) :
    x ∈ BubbleSet (fun _ : ℕ => Measure.dirac x) 1 := by
  intro r hr
  have : (fun _ : ℕ => (Measure.dirac x) (Metric.ball x r)) = fun _ : ℕ => (1 : ℝ≥0∞) := by
    funext n
    rw [MeasureTheory.Measure.dirac_apply_of_mem (Metric.mem_ball_self hr)]
  rw [this]
  simp

/-- **Uhlenbeck bubbling: finiteness of the concentration set.**

Let `mu n` be the sequence of energy measures of a sequence of Yang–Mills connections
(`mu n = |F_{A_n}|² dvol`) on a metric measure space `X`, subject to a uniform energy bound
`mu n (univ) ≤ E < ∞`.  Fix a concentration threshold `eps > 0` (the `ε` of `ε`-regularity).
Then the bubbling set — the set of points at which at least `eps` of the energy concentrates
at every scale — is *finite*, and its cardinality obeys the quantization bound
`#(bubbling set) * eps ≤ E`.

This is the combinatorial/measure-theoretic core of Uhlenbeck's compactness theorem: away from
these finitely many points, the `ε`-regularity theorem applies and gives local convergence,
while each bubble point absorbs at least `eps` of energy. -/
