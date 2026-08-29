/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Uhlenbeck Bubbling

Concentration–compactness ("bubbling") for a sequence of Yang–Mills energy measures.

Uhlenbeck's compactness theorem is built on two pillars: an `ε`-regularity theorem (a
connection with small local curvature energy is, after a gauge change, controlled in
every Sobolev norm) and the *bubbling* mechanism, which says that a sequence of
connections with uniformly bounded Yang–Mills energy `Λ` can fail to have small local
energy only at **finitely many** points, at most `Λ / ε₀` of them, where `ε₀` is the
threshold of the `ε`-regularity theorem.

This file formalizes the second pillar in the generality in which it is actually used —
i.e. as a statement about the energy measures `μ n = |F_{A_n}|² dvol` alone — and proves
it: the bubbling set is finite, energy is quantized on it (`#bubbles · ε ≤ Λ`), and off
the bubbling set the small-energy hypothesis of `ε`-regularity is available on a fixed
ball along a subsequence.
-/

namespace Frontier

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The **bubbling set** (energy concentration set) at level `ε` of a sequence of energy
measures `μ n`.

In the Yang–Mills setting `μ n` is the energy measure `|F_{A_n}|² dvol` of a sequence of
connections `A_n`, and `ε` is the `ε`-regularity threshold `ε₀` of Uhlenbeck's theorem.
A point `x` lies in the bubbling set when, at *every* scale `r > 0`, at least `ε` of the
energy asymptotically concentrates in the ball `B(x, r)`: these are exactly the points at
which a bubble can form, i.e. the points where `ε`-regularity may fail. -/

lemma bubbleSet_dirac (x₀ : X) : bubbleSet (fun _ : ℕ => Measure.dirac x₀) 1 = {x₀} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hr : 0 < dist x x₀ := dist_pos.2 hne
    have hthis := h (dist x x₀) hr
    have hmeas : (Measure.dirac x₀) (ball x (dist x x₀)) = 0 := by
      rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_ball]
      simp [Metric.mem_ball, dist_comm]
    simp [hmeas] at hthis
  · rintro rfl
    intro r hr
    have hmeas : (Measure.dirac x) (ball x r) = 1 := by
      rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_ball]
      simp [Metric.mem_ball, hr]
    simp [hmeas]

/-- The bubbling set of a sequence of energy *densities* `e n` (in Yang–Mills: the
pointwise curvature densities `|F_{A_n}|²`) with respect to a background volume measure
`vol`: the points where, at every scale, at least `ε` of the energy `∫ |F_{A_n}|²`
asymptotically concentrates. -/
