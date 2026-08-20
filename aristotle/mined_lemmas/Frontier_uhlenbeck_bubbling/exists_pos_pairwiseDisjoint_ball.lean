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

theorem exists_pos_pairwiseDisjoint_ball {X : Type*} [MetricSpace X] (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint (fun x => ball x r) := by
  obtain ⟨C, hC0, hC⟩ := (T.finite_toSet).relatively_discrete
  set C' : ℝ≥0∞ := min C 1 with hC'
  have hC'0 : 0 < C' := lt_min hC0 (by norm_num)
  have hC'top : C' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hpos : 0 < C'.toReal := ENNReal.toReal_pos hC'0.ne' hC'top
  refine ⟨C'.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have hle : C' ≤ edist x y := le_trans (min_le_left _ _) (hC x hx y hy hxy)
  have : C'.toReal ≤ (edist x y).toReal :=
    ENNReal.toReal_mono (edist_ne_top x y) hle
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this
  linarith

/-- **Energy quantization bound.**  Any finite set of bubbling points has cardinality at
most `E / ε₀`, stated multiplicatively. -/
