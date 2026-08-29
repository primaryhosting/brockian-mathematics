/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

theorem abc_bounded_imp_finite (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := h (ε / 2) (by linarith)
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hK : ∀ a b c : ℕ, ABCTriple a b c →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ht
    refine le_trans (hK₀ a b c ht) ?_
    have hpos : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  set M : ℝ := K ^ (2 / ε) with hMdef
  set N : ℕ := ⌈K * M ^ (1 + ε / 2)⌉₊ with hNdef
  apply Set.Finite.subset
    (((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N))))
  rintro ⟨a, b, c⟩ ⟨ht, hlt⟩
  obtain ⟨ha, hb, habc, hcop⟩ := ht
  -- bound the radical
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have hr1 : (1 : ℝ) ≤ r := one_le_rad (a * b * c)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hub : (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hK a b c ⟨ha, hb, habc, hcop⟩
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hpos2 : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hkey : r ^ (ε / 2) < K := by
    have : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      rw [← hsplit]; exact lt_of_lt_of_le hlt hub
    nlinarith [hpos2]
  have hrM : r < M := by
    have h2 : (0 : ℝ) < 2 / ε := by positivity
    have := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ r ^ (ε / 2)) hkey h2
    rw [← Real.rpow_mul (le_of_lt hr0)] at this
    have he : ε / 2 * (2 / ε) = 1 := by field_simp
    rw [he, Real.rpow_one] at this
    exact this
  have hcM : (c : ℝ) ≤ K * M ^ (1 + ε / 2) := by
    refine le_trans hub ?_
    have : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hr0) (le_of_lt hrM) (by linarith)
    exact mul_le_mul_of_nonneg_left this (le_of_lt hK0)
  have hcN : c ≤ N := by
    have : (⌈(c : ℝ)⌉₊ : ℕ) ≤ N := Nat.ceil_le_ceil hcM
    simpa using this
  have habc' : a + b = c := habc
  have hac : a ≤ c := by omega
  have hbc : b ≤ c := by omega
  exact ⟨le_trans hac hcN, le_trans hbc hcN, hcN⟩

/-- The exceptional sets shrink as `ε` grows. -/
