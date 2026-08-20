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

lemma abc_conjecture_of_bounded (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by linarith)
  -- a uniform bound on `c` for exceptional triples
  have hKpos : (0 : ℝ) < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set K' : ℝ := max K 1 with hK'
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'bound : ∀ a b c : ℕ, ABCTriple a b c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ht
    refine le_trans (hK a b c ht) ?_
    have hpow : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  set M : ℝ := K' * (K' ^ (2 / ε)) ^ (1 + ε / 2) with hM
  have key : ∀ p ∈ exceptionalSet ε, (p.2.2 : ℝ) ≤ M := by
    rintro ⟨a, b, c⟩ ⟨ht, hexc⟩
    simp only at ht hexc
    set R : ℝ := (rad (a * b * c) : ℝ) with hR
    have hR1 : (1 : ℝ) ≤ R := one_le_rad_real _
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
    have hsplit : R ^ (1 + ε) = R ^ (1 + ε / 2) * R ^ (ε / 2) := by
      rw [← Real.rpow_add hRpos]; ring_nf
    have hupper : (c : ℝ) ≤ K' * R ^ (1 + ε / 2) := hK'bound a b c ht
    have hhalfpos : (0 : ℝ) < R ^ (1 + ε / 2) := Real.rpow_pos_of_pos hRpos _
    have hlt : R ^ (1 + ε / 2) * R ^ (ε / 2) < K' * R ^ (1 + ε / 2) := by
      rw [← hsplit]; linarith
    have hRe : R ^ (ε / 2) < K' := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hlt, hhalfpos]
    have hRle : R ≤ K' ^ (2 / ε) := by
      have h1 : (R ^ (ε / 2)) ^ (2 / ε) = R := by
        rw [← Real.rpow_mul hRpos.le]
        rw [show (ε / 2) * (2 / ε) = 1 by field_simp]
        exact Real.rpow_one R
      calc R = (R ^ (ε / 2)) ^ (2 / ε) := h1.symm
        _ ≤ K' ^ (2 / ε) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hRpos.le _) hRe.le (by positivity)
    have : R ^ (1 + ε / 2) ≤ (K' ^ (2 / ε)) ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hRpos) hRle (by linarith)
    calc (c : ℝ) ≤ K' * R ^ (1 + ε / 2) := hupper
      _ ≤ K' * (K' ^ (2 / ε)) ^ (1 + ε / 2) := by
          exact mul_le_mul_of_nonneg_left this (le_of_lt hKpos)
  -- hence the exceptional set is contained in a finite box
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsub : exceptionalSet ε ⊆ Set.Iic N ×ˢ (Set.Iic N ×ˢ Set.Iic N) := by
    rintro ⟨a, b, c⟩ hp
    have hc : (c : ℝ) ≤ M := key _ hp
    have hcN : c ≤ N := by
      have : (c : ℝ) < (N : ℝ) := lt_of_le_of_lt hc hN
      exact_mod_cast le_of_lt this
    obtain ⟨ht, -⟩ := hp
    have hsum := ht.hsum
    have hb := ht.hb
    have ha := ht.ha
    dsimp only at hsum hb ha
    exact ⟨show a ≤ N by omega, show b ≤ N by omega, show c ≤ N by omega⟩
  exact Set.Finite.subset ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod
    (Set.finite_Iic N))) hsub

/-- **A Lean-checked reduction for the abc conjecture.**
The finiteness form of the abc conjecture (for every `ε > 0` only finitely many coprime
triples `a + b = c` satisfy `c > rad (a * b * c) ^ (1 + ε)`) is equivalent to its
effective-constant form (for every `ε > 0` there is `K` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime triples `a + b = c`). -/
