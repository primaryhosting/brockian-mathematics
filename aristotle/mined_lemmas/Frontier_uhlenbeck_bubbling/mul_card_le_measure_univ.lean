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
open scoped ENNReal

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

This file formalizes the *bubbling* (energy concentration) part of Uhlenbeck compactness for
Yang–Mills connections, in the measure-theoretic form in which it is used.

A sequence of connections `A n` on a bundle over a Riemannian manifold `X` gives rise to the
sequence of *energy measures* `mu n = |F_{A n}|² dvol`, and a uniform energy bound
`mu n X ≤ E < ∞` is the standing hypothesis of Uhlenbeck's theorem.  The analytic heart of the
theorem (ε-regularity) provides a threshold `eps > 0` below which the connections converge
smoothly, so that failure of compactness is confined to the *bubble set*: those points where
every ball eventually carries at least `eps` of energy.

The results proved here are the quantization/counting half of the statement, which is the part
that is purely about the energy measures:

* `Frontier.uhlenbeck_bubbling` : the bubble set is **finite** and
  `eps * (number of bubbles) ≤ E`;
* `Frontier.uhlenbeck_bubbling_ncard_le` : hence at most `E / eps` bubbles;
* `Frontier.bubbleSet_eq_empty_of_energy_lt` : **base case / removable singularity**, if the
  total energy stays below the ε-regularity threshold, no bubbling occurs at all;
* `Frontier.bubbleSet_const` : for a single limiting energy measure, bubble points are exactly
  the atoms of mass at least `eps` — bubbling is concentration of energy in atoms;
* `Frontier.bubbleSet_const_eq_empty_of_noAtoms` : a non-atomic limiting energy measure has no
  bubbles (removable singularity for the limit);
* `Frontier.uhlenbeck_bubbling_energyDensity` : the same statement phrased directly for
  curvature energy densities `|F_{A n}|²` integrated against the volume measure.
-/

namespace Frontier

open MeasureTheory Filter Metric Set

section Separation

variable {X : Type*} [MetricSpace X]

/-- A finite set of points in a metric space can be surrounded by pairwise disjoint balls
of a common positive radius. -/

lemma mul_card_le_measure_univ (mu : Measure X) (eps : ℝ≥0∞) (T : Finset X) (r : ℝ)
    (hdisj : (↑T : Set X).PairwiseDisjoint (fun x => Metric.ball x r))
    (h : ∀ x ∈ T, eps ≤ mu (Metric.ball x r)) :
    eps * T.card ≤ mu Set.univ := by
  have hsum : mu (⋃ x ∈ T, Metric.ball x r) = ∑ x ∈ T, mu (Metric.ball x r) :=
    measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)
  calc eps * T.card = ∑ _x ∈ T, eps := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ T, mu (Metric.ball x r) := Finset.sum_le_sum h
    _ = mu (⋃ x ∈ T, Metric.ball x r) := hsum.symm
    _ ≤ mu Set.univ := measure_mono (Set.subset_univ _)

/-- The **bubble set** (concentration set) of a sequence of energy measures `mu n` at
threshold `eps`: the points `x` such that on *every* ball around `x`, the energy is
eventually at least `eps`.

In the Yang–Mills setting, `mu n` is the energy measure `|F_{A n}|² dvol` of a sequence of
connections `A n`, and `bubbleSet mu eps` is the set of points where bubbling occurs, `eps`
being the ε-regularity threshold. -/
