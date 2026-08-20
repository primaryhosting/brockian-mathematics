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

theorem card_mul_le_of_subset_bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : ℕ → Measure X) (E ε₀ : ℝ≥0∞)
    (hε₀ : ε₀ ≠ 0) (hε₀' : ε₀ ≠ ⊤) (hbound : ∀ i, ν i Set.univ ≤ E)
    (T : Finset X) (hT : ↑T ⊆ bubbleSet ν ε₀) :
    (T.card : ℝ≥0∞) * ε₀ ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_ball T
  -- It suffices to bound `T.card * c` for every `c < ε₀`.
  have key : ∀ c : ℝ≥0∞, c < ε₀ → (T.card : ℝ≥0∞) * c ≤ E := by
    intro c hc
    have hev : ∀ᶠ i in atTop, ∀ x ∈ T, c < ν i (ball x r) := by
      rw [eventually_all_finset]
      intro x hx
      exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hT hx r hr))
    obtain ⟨i, hi⟩ := hev.exists
    calc (T.card : ℝ≥0∞) * c = ∑ _x ∈ T, c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ T, ν i (ball x r) := Finset.sum_le_sum fun x hx => (hi x hx).le
      _ = ν i (⋃ x ∈ T, ball x r) :=
          (measure_biUnion_finset hdisj fun x _ => measurableSet_ball).symm
      _ ≤ ν i Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ E := hbound i
  -- Now let `c ↑ ε₀`.
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  have hlt : a * ε₀ < ε₀ := by
    calc a * ε₀ = ε₀ * a := mul_comm _ _
      _ < ε₀ * 1 := ENNReal.mul_lt_mul_right hε₀ hε₀' ha
      _ = ε₀ := mul_one _
  calc a * ((T.card : ℝ≥0∞) * ε₀) = (T.card : ℝ≥0∞) * (a * ε₀) := by ring
    _ ≤ E := key _ hlt

/-! ## Main theorem -/

/-- **Uhlenbeck bubbling: finiteness and energy quantization of the bubbling set.**

If `ν : ℕ → Measure X` is a sequence of energy measures on a metric space with total mass
uniformly bounded by `E < ∞`, and `ε₀ ∈ (0, ∞)` is a concentration threshold, then the set
of bubbling points — the points at which at least `ε₀` of energy concentrates in every
ball, in the `liminf` sense — is finite, and its cardinality `N` satisfies `N · ε₀ ≤ E`;
that is, at most `E / ε₀` bubbles can form. -/
