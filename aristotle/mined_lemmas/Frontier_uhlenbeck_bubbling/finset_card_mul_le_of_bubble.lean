import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Metric Set

/-- A point `x` is an *energy concentration point* (a *bubble point*) at level `eps`
for a sequence of energy measures `mu n` (think: `mu n = |F_{A n}|² dvol`, the Yang–Mills
energy density of a sequence of connections `A n`) if on *every* ball around `x` the
asymptotic energy is at least `eps`. -/

theorem finset_card_mul_le_of_bubble {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (mu : ℕ → Measure X) (Lam eps : ℝ≥0∞)
    (hbound : ∀ n, mu n Set.univ ≤ Lam) (S : Finset X)
    (hS : ∀ x ∈ S, BubblePoint mu eps x) :
    (S.card : ℝ≥0∞) * eps ≤ Lam := by
  refine nat_mul_le_of_forall_lt _ _ _ ?_
  intro c hc
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_balls S
  have hev : ∀ x ∈ S, ∀ᶠ n in atTop, c < mu n (Metric.ball x r) := fun x hx =>
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hS x hx r hr))
  have hall : ∀ᶠ n in atTop, ∀ x ∈ S, c < mu n (Metric.ball x r) :=
    (Filter.eventually_all_finset S).2 hev
  obtain ⟨n, hn⟩ := hall.exists
  calc (S.card : ℝ≥0∞) * c = ∑ _x ∈ S, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, mu n (Metric.ball x r) := Finset.sum_le_sum fun x hx => (hn x hx).le
    _ = mu n (⋃ x ∈ S, Metric.ball x r) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ mu n Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ Lam := hbound n

/-- The blow-up set is finite whenever the energies are uniformly bounded by a finite
`Lam` and the concentration level `eps` is positive. -/
