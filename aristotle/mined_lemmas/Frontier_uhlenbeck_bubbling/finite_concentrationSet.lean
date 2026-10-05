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

theorem finite_concentrationSet (E : ℕ → Measure X) (Λ ε : ℝ≥0∞) (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hb : ∀ n, E n Set.univ ≤ Λ) : (concentrationSet E ε).Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- choose `N` with `Λ < N * ε`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Λ < (N : ℝ≥0∞) * ε := by
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨1, by simpa [ENNReal.mul_top, hε] using lt_top_iff_ne_top.2 hΛ⟩
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (r := Λ / ε)
        (by simp [ENNReal.div_eq_top, hε, hΛ])
      refine ⟨N, ?_⟩
      have := (ENNReal.div_lt_iff (Or.inl hε) (Or.inl hεtop)).1 hN
      simpa [mul_comm] using this
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq N
  have := card_mul_le_of_subset_concentrationSet E Λ ε hb T hTsub
  rw [hTcard] at this
  exact absurd this (not_le.2 hN)

/-- The `limsup` analogue of `concentrationSet`. -/
