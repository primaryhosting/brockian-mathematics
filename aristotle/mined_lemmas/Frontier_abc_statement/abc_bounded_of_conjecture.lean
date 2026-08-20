/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma abc_bounded_of_conjecture (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ × ℕ), ↑S = exceptionalSet ε :=
    ⟨(h ε hε).toFinset, by simp⟩
  refine ⟨1 + ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε), ?_⟩
  intro a b c ht
  set R : ℝ := (rad (a * b * c) : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := one_le_rad_real _
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hpow : (1 : ℝ) ≤ R ^ (1 + ε) :=
    Real.one_le_rpow hR1 (by linarith)
  have hpowpos : (0 : ℝ) < R ^ (1 + ε) := lt_of_lt_of_le zero_lt_one hpow
  have hnonneg : ∀ p ∈ S, (0 : ℝ) ≤
      (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) := by
    intro p _
    positivity
  set K : ℝ := 1 + ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) with hK
  have hsum_nonneg : (0 : ℝ) ≤ ∑ p ∈ S, (p.2.2 : ℝ) /
      ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) := Finset.sum_nonneg hnonneg
  have hK1 : (1 : ℝ) ≤ K := by simp only [hK]; linarith
  by_cases hex : ((a, b, c) : ℕ × ℕ × ℕ) ∈ exceptionalSet ε
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ S := by rw [← hS] at hex; exact_mod_cast hex
    have hle : (c : ℝ) / R ^ (1 + ε) ≤
        ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) :=
      Finset.single_le_sum hnonneg hmem
    have : (c : ℝ) / R ^ (1 + ε) ≤ K := by simp only [hK]; linarith
    calc (c : ℝ) = ((c : ℝ) / R ^ (1 + ε)) * R ^ (1 + ε) := by
              field_simp
      _ ≤ K * R ^ (1 + ε) := by
              exact mul_le_mul_of_nonneg_right this (le_of_lt hpowpos)
  · have : ¬ (R ^ (1 + ε) < (c : ℝ)) := by
      intro hc
      exact hex ⟨ht, hc⟩
    push_neg at this
    calc (c : ℝ) ≤ R ^ (1 + ε) := this
      _ ≤ K * R ^ (1 + ε) := by nlinarith

