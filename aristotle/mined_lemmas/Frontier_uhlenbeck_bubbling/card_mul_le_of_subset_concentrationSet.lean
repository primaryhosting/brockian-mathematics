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

theorem card_mul_le_of_subset_concentrationSet (E : ℕ → Measure X) (Λ ε : ℝ≥0∞)
    (hb : ∀ n, E n Set.univ ≤ Λ) (T : Finset X) (hT : ↑T ⊆ concentrationSet E ε) :
    (T.card : ℝ≥0∞) * ε ≤ Λ := by
  classical
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_balls T
  have hsum : ∀ n, ∑ x ∈ T, E n (ball x r) ≤ Λ := by
    intro n
    have hmeas : ∀ x ∈ T, MeasurableSet (ball x r) := fun x _ => measurableSet_ball
    have := measure_biUnion_finset (μ := E n) hdisj hmeas
    calc ∑ x ∈ T, E n (ball x r) = E n (⋃ x ∈ T, ball x r) := this.symm
      _ ≤ E n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ Λ := hb n
  calc (T.card : ℝ≥0∞) * ε = ∑ _x ∈ T, ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ T, liminf (fun n => E n (ball x r)) atTop :=
        Finset.sum_le_sum fun x hx => hT (Finset.mem_coe.2 hx) r hr
    _ ≤ liminf (fun n => ∑ x ∈ T, E n (ball x r)) atTop :=
        sum_liminf_le_liminf_sum T fun x n => E n (ball x r)
    _ ≤ liminf (fun _ : ℕ => Λ) atTop :=
        liminf_le_liminf (Eventually.of_forall hsum)
    _ = Λ := liminf_const Λ

/-- With a finite uniform mass bound and a positive concentration threshold, the
set of concentration points is finite. -/
