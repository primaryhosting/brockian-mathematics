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

lemma exists_radius_pairwiseDisjoint_ball (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint (fun x => Metric.ball x r) := by
  classical
  set P : Finset (X × X) := (T ×ˢ T).filter (fun p => p.1 ≠ p.2) with hP
  have hmem : ∀ x y : X, x ∈ T → y ∈ T → x ≠ y → (x, y) ∈ P := by
    intro x y hx hy hxy
    simp [hP, Finset.mem_filter, Finset.mem_product, hx, hy, hxy]
  rcases P.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have hmemP := hmem x y hx hy hxy
    rw [hemp] at hmemP
    exact absurd hmemP (Finset.notMem_empty _)
  · obtain ⟨p, hpP, hpmin⟩ := P.exists_min_image (fun p => dist p.1 p.2) hne
    have hp : p.1 ≠ p.2 := by
      have hpP' := hpP
      simp only [hP, Finset.mem_filter] at hpP'
      exact hpP'.2
    have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hp
    refine ⟨dist p.1 p.2 / 2, by linarith, ?_⟩
    intro x hx y hy hxy
    have hxy' := hpmin (x, y) (hmem x y hx hy hxy)
    exact Metric.ball_disjoint_ball (by simpa using by linarith [hxy'])

end Separation

section Bubbles

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- If finitely many balls of radius `r` centred at points of `T` are pairwise disjoint and
each carries at least energy `eps`, then `eps * #T` is at most the total energy. -/
