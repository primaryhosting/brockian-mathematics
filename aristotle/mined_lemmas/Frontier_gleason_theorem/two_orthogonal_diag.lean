/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28's module system forbids a `/-!` module docstring before `import`;
-- the header above is therefore a plain block comment and is repeated below.)

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *quantum measure* on a finite dimensional complex Hilbert space `ℂⁿ` is a map `μ` from the
orthogonal projections to `ℝ` which is nonnegative, finitely additive on orthogonal pairs, and
normalized (`μ 1 = 1`).  Gleason's theorem says that in dimension at least three every such `μ`
is given by the Born rule `μ P = Tr(ρ P)` for a unique density operator `ρ`.

This file contains:

* `Frontier.QuantumMeasure`, `Frontier.IsDensity`, `Frontier.Represents`: the formalized
  statement ingredients;
* `Frontier.born_rule_quantumMeasure`: every density operator gives a quantum measure;
* `Frontier.density_of_positive_linear`: a linear functional on matrices that is nonnegative
  on projections and normalized is the trace against a density operator;
* `Frontier.density_unique`: the density operator representing a measure is unique;
* `Frontier.gleason_theorem`: the Lean-checked reduction of Gleason's theorem to the linearity
  of the frame function (the analytic heart of the classical proof);
* `Frontier.gleason_fails_in_dimension_two`: an explicit quantum measure on the projections of
  `ℂ²` that is represented by no operator, showing that the dimension hypothesis is necessary.
-/

open Matrix Complex
open scoped ComplexOrder

namespace Frontier

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal projection: a Hermitian idempotent matrix. -/

lemma two_orthogonal_diag {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProjection P)
    (hQ : IsProjection Q) (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P 0 0).re + (Q 0 0).re = 1 ∨ (P 0 0).re = 0 ∨ (Q 0 0).re = 0 := by
  obtain ⟨hp00, hp11, hp10, hpsq, hpoff⟩ := proj_two_relations hP
  obtain ⟨hq00, hq11, hq10, hqsq, hqoff⟩ := proj_two_relations hQ
  have m00 : P 0 0 * Q 0 0 + P 0 1 * Q 1 0 = 0 := by
    have := congrFun (congrFun hPQ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have m01 : P 0 0 * Q 0 1 + P 0 1 * Q 1 1 = 0 := by
    have := congrFun (congrFun hPQ 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have n00 : Q 0 0 * P 0 0 + Q 0 1 * P 1 0 = 0 := by
    have := congrFun (congrFun hQP 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  by_cases hb : P 0 1 = 0
  · have ha : (P 0 0).re * ((P 0 0).re - 1) = 0 := by
      have : Complex.normSq (P 0 1) = 0 := by simp [hb]
      nlinarith [hpsq, this]
    rcases mul_eq_zero.mp ha with h | h
    · exact Or.inr (Or.inl h)
    · have ha1 : P 0 0 = 1 := by
        rw [hp00]
        norm_num
        linarith
      have : Q 0 0 = 0 := by
        have := m00
        rw [ha1, hb] at this
        simpa using this
      exact Or.inr (Or.inr (by rw [this]; simp))
  by_cases hb' : Q 0 1 = 0
  · have hb'' : Q 1 0 = 0 := by rw [hq10, hb']; simp
    have ha : (Q 0 0).re * ((Q 0 0).re - 1) = 0 := by
      have : Complex.normSq (Q 0 1) = 0 := by simp [hb']
      nlinarith [hqsq, this]
    rcases mul_eq_zero.mp ha with h | h
    · exact Or.inr (Or.inr h)
    · have ha1 : Q 0 0 = 1 := by
        rw [hq00]
        norm_num
        linarith
      have : P 0 0 = 0 := by
        have := n00
        rw [ha1, hb'] at this
        simpa using this
      exact Or.inr (Or.inl (by rw [this]; simp))
  -- main case: both off-diagonal entries are nonzero
  left
  set a : ℝ := (P 0 0).re with ha
  set a' : ℝ := (Q 0 0).re with ha'
  have hnb : 0 < Complex.normSq (P 0 1) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_nonneg (P 0 1)).lt_of_ne'
      (by simpa [Complex.normSq_eq_zero] using hb)
  have hnb' : 0 < Complex.normSq (Q 0 1) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_nonneg (Q 0 1)).lt_of_ne'
      (by simpa [Complex.normSq_eq_zero] using hb')
  have hapos : 0 < a := by nlinarith [hpsq, hnb]
  have ha1 : a < 1 := by nlinarith [hpsq, hnb]
  have ha'pos : 0 < a' := by nlinarith [hqsq, hnb']
  have ha'1 : a' < 1 := by nlinarith [hqsq, hnb']
  -- the diagonal of `Q` is `(a', 1 - a')`
  have hq11' : Q 1 1 = (((1 - a' : ℝ)) : ℂ) := by
    have h := mul_eq_zero.mp hqoff
    rcases h with h | h
    · exact absurd h hb'
    · have : Q 1 1 = 1 - Q 0 0 := by linear_combination h
      rw [this, hq00]
      push_cast
      ring
  have heq : ((a : ℂ)) * Q 0 1 = -(P 0 1 * (((1 - a' : ℝ)) : ℂ)) := by
    have := m01
    rw [hp00, hq11'] at this
    linear_combination this
  have hnorm := congrArg Complex.normSq heq
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal] at hnorm
  -- turn the two idempotency relations into expressions for the off-diagonal norms
  have hnb_eq : Complex.normSq (P 0 1) = a - a ^ 2 := by linarith [hpsq]
  have hnb'_eq : Complex.normSq (Q 0 1) = a' - a' ^ 2 := by linarith [hqsq]
  rw [hnb_eq, hnb'_eq] at hnorm
  have key : a * (1 - a') * (a + a' - 1) = 0 := by nlinarith [hnorm]
  have h1 : a ≠ 0 := ne_of_gt hapos
  have h2 : (1 - a') ≠ 0 := by linarith
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h1
    · exact absurd h' h2
  · linarith

