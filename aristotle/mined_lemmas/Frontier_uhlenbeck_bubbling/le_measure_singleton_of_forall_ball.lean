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

lemma le_measure_singleton_of_forall_ball (mu : Measure X) [IsFiniteMeasure mu] (eps : ℝ≥0∞)
    (x : X) (h : ∀ r : ℝ, 0 < r → eps ≤ mu (Metric.ball x r)) : eps ≤ mu {x} := by
  have hint : (⋂ n : ℕ, Metric.ball x (1 / (n + 1) : ℝ)) = {x} := by
    ext y
    simp only [Set.mem_iInter, Metric.mem_ball, Set.mem_singleton_iff]
    constructor
    · intro hy
      by_contra hne
      have hpos : 0 < dist y x := dist_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (hy n) (not_lt.mpr (le_of_lt hn))
    · rintro rfl
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa using hn
  have hanti : Antitone (fun n : ℕ => Metric.ball x (1 / (n + 1) : ℝ)) := by
    intro m n hmn
    refine Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.succ_le_succ hmn
  have htend := MeasureTheory.tendsto_measure_iInter_atTop (μ := mu)
    (s := fun n : ℕ => Metric.ball x (1 / (n + 1) : ℝ))
    (fun _ => measurableSet_ball.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hint] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards with n
  exact h _ (by positivity)

/-- For a single finite energy measure, the bubble points are exactly the atoms of mass at
least `eps`: concentration of energy at a point *is* an atom of the energy measure. -/
