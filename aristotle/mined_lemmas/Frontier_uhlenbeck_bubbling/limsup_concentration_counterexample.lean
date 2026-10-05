import Mathlib
/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalisation of the *bubbling* (energy concentration) part of Uhlenbeck's
compactness theory for Yang–Mills connections.

Setting.  Let `X` be a metric measure space (think of a Riemannian four-manifold
with its volume measure `μ`) and let `A n` be a sequence of connections with
curvature `F_{A n}`.  All that enters the concentration analysis is the sequence
of energy densities `F n x = |F_{A n}(x)|²`, together with the uniform energy
bound `∫ |F_{A n}|² dμ ≤ Λ`.

A point `x` is an *`ε`-bubble point* of the sequence if, no matter how small a
ball we take around `x`, at least `ε` units of energy persistently sit inside
that ball, i.e. `ε ≤ liminf_n ∫_{B(x,r)} |F_{A n}|²`.  (Using `liminf` is the
same as passing to a subsequence along which the local energies converge, which
is how the statement is usually phrased; with `limsup` instead the statement is
*false*, see `Frontier.limsup_concentration_counterexample` below.)

Main result (`Frontier.uhlenbeck_bubbling`): the set of `ε`-bubble points is
finite, and the number of bubbles is controlled by the energy:
`(number of bubbles) * ε ≤ Λ`.  In particular at most `⌊Λ/ε⌋` bubbles can form,
and if the total energy is below the threshold `ε` no bubbling occurs at all.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace Frontier

section Auxiliary

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem limsup_concentration_counterexample :
    ∃ E : ℕ → Measure ℕ, (∀ n, E n Set.univ ≤ 1) ∧ (limsupConcentrationSet E 1).Infinite := by
  refine ⟨fun n => Measure.dirac (Nat.unpair n).1, fun n => by simp, ?_⟩
  have huniv : limsupConcentrationSet (fun n => Measure.dirac (Nat.unpair n).1) 1 = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    intro r hr
    refine le_limsup_of_frequently_le ?_
    rw [Filter.frequently_atTop]
    intro N
    refine ⟨Nat.pair x N, Nat.right_le_pair x N, ?_⟩
    simp only [Nat.unpair_pair]
    simp [Measure.dirac_apply' _ (measurableSet_ball (x := x) (ε := r)), Metric.mem_ball_self hr]
  rw [huniv]
  exact Set.infinite_univ

end AbstractConcentration

section YangMills

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- `bubbleSet μ F ε` is the set of `ε`-bubble points of a sequence of Yang–Mills
connections whose curvature energy densities are `F n` (i.e. `F n x = |F_{A n}(x)|²`)
on the metric measure space `(X, μ)`:  points where, in every ball, at least `ε`
of the energy persists in the limit. -/
