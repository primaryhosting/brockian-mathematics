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

lemma exists_radius_pairwiseDisjoint_ball (s : Finset X) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (ball x r) (ball y r) := by
  obtain ⟨C, hC, hCs⟩ := (s.finite_toSet).relatively_discrete
  set D : ℝ≥0∞ := min C 1 with hD
  have hD0 : D ≠ 0 := by simp [hD, hC.ne']
  have hDtop : D ≠ ⊤ := by simp [hD]
  have hpos : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
  refine ⟨D.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have h1 : D ≤ edist x y := le_trans (min_le_left _ _) (hCs x hx y hy hxy)
  have h2 : D.toReal ≤ dist x y := by
    have := ENNReal.toReal_mono (by simp [edist_dist]) h1
    simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using this
  linarith

omit [BorelSpace X] in
/-- Off the bubbling set, the energy in some fixed small ball drops below the threshold `ε`
along a subsequence: this is precisely the hypothesis of Uhlenbeck's `ε`-regularity
theorem. -/
