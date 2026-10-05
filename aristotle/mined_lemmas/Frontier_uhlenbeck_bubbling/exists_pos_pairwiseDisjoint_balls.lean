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

theorem exists_pos_pairwiseDisjoint_balls {X : Type*} [MetricSpace X] (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint fun x => ball x r := by
  classical
  rcases T.offDiag.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    have hmem : ((x, y) : X × X) ∈ T.offDiag :=
      Finset.mem_offDiag.2 ⟨Finset.mem_coe.1 hx, Finset.mem_coe.1 hy, hxy⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · set d : ℝ := T.offDiag.inf' h fun p => dist p.1 p.2 with hd_def
    have hd : 0 < d := by
      rw [hd_def, Finset.lt_inf'_iff]
      intro p hp
      exact dist_pos.2 (Finset.mem_offDiag.1 hp).2.2
    refine ⟨d / 2, by positivity, fun x hx y hy hxy => ?_⟩
    have hmem : ((x, y) : X × X) ∈ T.offDiag :=
      Finset.mem_offDiag.2 ⟨Finset.mem_coe.1 hx, Finset.mem_coe.1 hy, hxy⟩
    have hxy' : d ≤ dist x y := Finset.inf'_le (fun p => dist p.1 p.2) hmem
    exact ball_disjoint_ball (by linarith)

end Auxiliary

section AbstractConcentration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The set of points at which a sequence of (energy) measures `E` concentrates at
least `ε` of mass in every ball, in the `liminf` sense. -/
