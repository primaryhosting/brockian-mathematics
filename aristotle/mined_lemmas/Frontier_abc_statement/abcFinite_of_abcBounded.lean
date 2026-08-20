/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

lemma abcFinite_of_abcBounded (h : ABCBounded) : ABCFinite := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := h (ε / 2) (by linarith)
  set B : ℝ := K ^ (2 / ε) with hB
  have hB0 : 0 < B := Real.rpow_pos_of_pos hK _
  set M : ℝ := K * B ^ (1 + ε / 2) with hM
  have hM0 : 0 ≤ M := by
    have : (0:ℝ) < B ^ (1 + ε / 2) := Real.rpow_pos_of_pos hB0 _
    positivity
  set N : ℕ := ⌈M⌉₊ with hN
  apply Set.Finite.subset ((Set.finite_Iic N).prod
    ((Set.finite_Iic N).prod (Set.finite_Iic N)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hc⟩
  dsimp only at ha hb hab habc hc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := one_le_rad_real _
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have hcb : (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hbound a b c ha hb hab habc
  have hrpow : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hpos : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hkey : r ^ (ε / 2) < K := by
    have h1 : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      rw [← hrpow]; exact lt_of_lt_of_le hc hcb
    nlinarith
  have hrB : r ≤ B := by
    by_contra hlt
    push_neg at hlt
    have : B ^ (ε / 2) < r ^ (ε / 2) :=
      Real.rpow_lt_rpow (le_of_lt hB0) hlt (by linarith)
    have hBe : B ^ (ε / 2) = K := by
      rw [hB, ← Real.rpow_mul (le_of_lt hK)]
      rw [show 2 / ε * (ε / 2) = 1 by field_simp]
      simp
    rw [hBe] at this
    linarith
  have hcM : (c : ℝ) ≤ M := by
    have : r ^ (1 + ε / 2) ≤ B ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hrB (by linarith)
    calc (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hcb
      _ ≤ K * B ^ (1 + ε / 2) := by nlinarith
  have hcN : c ≤ N := by
    have : (c : ℝ) ≤ (N : ℝ) := le_trans hcM (Nat.le_ceil M)
    exact_mod_cast this
  have hac : a ≤ c := by omega
  have hbc : b ≤ c := by omega
  exact ⟨le_trans hac hcN, le_trans hbc hcN, hcN⟩

/-- The two standard formulations of the `abc` conjecture are equivalent. -/
