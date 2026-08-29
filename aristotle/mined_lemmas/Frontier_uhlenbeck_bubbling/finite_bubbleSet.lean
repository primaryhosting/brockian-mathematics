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

lemma finite_bubbleSet {μ : ℕ → Measure X} {Λ ε : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hbound : ∀ n : ℕ, μ n Set.univ ≤ Λ) :
    (bubbleSet μ ε).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hΛ hε).ne
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq k
  have hle := card_mul_le_of_subset_bubbleSet hbound t hts
  rw [htc] at hle
  rw [ENNReal.div_lt_iff (Or.inl hε) (Or.inr hΛ)] at hk
  exact absurd hle (not_le_of_gt hk)

/-- **Uhlenbeck bubbling / concentration–compactness for Yang–Mills energies.**

Let `μ n` be the energy measures `|F_{A_n}|² dvol` of a sequence of connections with
uniformly bounded Yang–Mills energy `Λ < ∞`, and let `ε > 0` be the `ε`-regularity
threshold of Uhlenbeck's theorem.  Then:

* the bubbling set (the set of points where at least `ε` of energy concentrates at every
  scale) is **finite**;
* its cardinality is bounded by `Λ / ε`, in the quantized form `#bubbles · ε ≤ Λ`;
* at every point *outside* the bubbling set there is a fixed ball on which, along a
  subsequence, the energy stays below the threshold `ε` — the small-energy hypothesis
  from which Uhlenbeck's `ε`-regularity yields local convergence (after gauge change)
  away from the finitely many bubble points. -/
