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

theorem uhlenbeck_bubbling_energyDensity (vol : Measure X) (F : ℕ → X → ℝ≥0∞) {E eps : ℝ≥0∞} (heps : eps ≠ 0) (hE : E ≠ ⊤)
    (hbdd : ∀ n, ∫⁻ x, F n x ∂vol ≤ E) :
    let S : Set X := {x : X | ∀ r : ℝ, 0 < r →
      ∀ᶠ n in atTop, eps ≤ ∫⁻ y in Metric.ball x r, F n y ∂vol}
    S.Finite ∧ eps * S.ncard ≤ E ∧ (S.ncard : ℝ≥0∞) ≤ E / eps := by
  intro S
  set mu : ℕ → Measure X := fun n => vol.withDensity (F n) with hmu
  have hball : ∀ (n : ℕ) (x : X) (r : ℝ),
      mu n (Metric.ball x r) = ∫⁻ y in Metric.ball x r, F n y ∂vol := by
    intro n x r
    rw [hmu, withDensity_apply _ measurableSet_ball]
  have hSeq : S = bubbleSet mu eps := by
    ext x
    simp only [S, bubbleSet, Set.mem_setOf_eq, hball]
  have hbdd' : ∀ n, mu n Set.univ ≤ E := by
    intro n
    rw [hmu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hbdd n
  rw [hSeq]
  exact ⟨(uhlenbeck_bubbling heps hE hbdd').1, (uhlenbeck_bubbling heps hE hbdd').2,
    uhlenbeck_bubbling_ncard_le heps hE hbdd'⟩

end YangMillsEnergy

end Frontier

