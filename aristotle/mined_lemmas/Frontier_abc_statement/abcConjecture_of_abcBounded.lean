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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/

theorem abcConjecture_of_abcBounded (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := h (ε / 2) (by positivity)
  -- we may assume `K ≥ 1`
  set K' : ℝ := max K 1 with hK'def
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le zero_lt_one hK'1
  have hK' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ha hb hab hsum
    refine le_trans (hK a b c ha hb hab hsum) ?_
    have : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_rad_real _)) _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  set M : ℝ := Real.exp (2 * Real.log K' / ε) with hMdef
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ 2 * Real.log K' / ε := by
      have : 0 ≤ Real.log K' := Real.log_nonneg hK'1
      positivity
    simpa using Real.exp_le_exp.2 this
  set B : ℝ := K' * M ^ (1 + ε / 2) with hBdef
  set N : ℕ := ⌈B⌉₊ with hNdef
  have key : ∀ t ∈ abcExceptions ε, t.1 ≤ N ∧ t.2.1 ≤ N ∧ t.2.2 ≤ N := by
    rintro ⟨a, b, c⟩ ⟨ha, hb, hab, hsum, hlt⟩
    simp only at ha hb hab hsum hlt
    set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
    have hr1 : (1 : ℝ) ≤ r := one_le_rad_real _
    have hub : (c : ℝ) ≤ K' * r ^ (1 + ε / 2) := hK' a b c ha hb hab hsum
    have hstep : r ^ (1 + ε) < K' * r ^ (1 + ε / 2) := lt_of_lt_of_le hlt hub
    have hrM : r ≤ M := rad_le_of_lt ε K' r hε hr1 hstep
    have hcB : (c : ℝ) ≤ B := by
      refine le_trans hub ?_
      rw [hBdef]
      have : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
        Real.rpow_le_rpow (by linarith) hrM (by linarith)
      exact mul_le_mul_of_nonneg_left this hK'0.le
    have hcN : c ≤ N := by
      have : (c : ℝ) ≤ (N : ℝ) := le_trans hcB (by rw [hNdef]; exact Nat.le_ceil B)
      exact_mod_cast this
    refine ⟨?_, ?_, hcN⟩
    · dsimp only
      omega
    · dsimp only
      omega
  refine Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)))) ?_
  intro t ht
  obtain ⟨h1, h2, h3⟩ := key t ht
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  exact ⟨by omega, by omega, by omega⟩

