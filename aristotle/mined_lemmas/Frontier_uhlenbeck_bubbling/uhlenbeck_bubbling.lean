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

theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : ℕ → Measure X) (E ε₀ : ℝ≥0∞)
    (hE : E ≠ ⊤) (hε₀ : ε₀ ≠ 0) (hε₀' : ε₀ ≠ ⊤) (hbound : ∀ i, ν i Set.univ ≤ E) :
    (bubbleSet ν ε₀).Finite ∧ ((bubbleSet ν ε₀).ncard : ℝ≥0∞) * ε₀ ≤ E := by
  have key := card_mul_le_of_subset_bubbleSet ν E ε₀ hε₀ hε₀' hbound
  have hfin : (bubbleSet ν ε₀).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨n, hn⟩ : ∃ n : ℕ, E < n * ε₀ := by
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (r := E / ε₀)
        (by simp [ENNReal.div_eq_top, hε₀, hE])
      exact ⟨n, by rwa [ENNReal.div_lt_iff (Or.inl hε₀) (Or.inl hε₀')] at hn⟩
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq n
    exact absurd (key T hTsub) (by rw [hTcard]; exact not_le.2 hn)
  refine ⟨hfin, ?_⟩
  have := key hfin.toFinset (by rw [hfin.coe_toFinset])
  rwa [← Set.ncard_eq_toFinset_card _ hfin] at this

/-- **Uhlenbeck bubbling for Yang–Mills energy measures on Euclidean space.**

For a sequence of curvature fields `F i : ℝⁿ → V` with Yang–Mills energies
`∫ ‖F i‖² ≤ E < ∞`, the set of points where at least `ε₀` of energy concentrates is
finite, with at most `E / ε₀` points. -/
