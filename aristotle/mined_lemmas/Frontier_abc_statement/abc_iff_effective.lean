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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`. -/

theorem abc_iff_effective : AbcConjecture ↔ AbcEffective := by
  constructor
  · intro h eps heps
    obtain ⟨C, hC⟩ := abcExceptions_bounded_of_finite eps (h eps heps)
    refine ⟨(C : ℝ) + 1, ?_⟩
    intro a b c ha hb hab hsum
    have hK1 : (1 : ℝ) ≤ (C : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
      linarith
    have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + eps) :=
      one_le_rad_rpow _ (by linarith)
    by_cases hex : ((rad (a * b * c) : ℝ) ^ (1 + eps) < (c : ℝ))
    · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ abcExceptions eps := ⟨ha, hb, hab, hsum, hex⟩
      have : (c : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC _ hmem
      nlinarith
    · push_neg at hex
      nlinarith
  · intro h eps heps
    obtain ⟨K, hK⟩ := h (eps / 2) (by linarith)
    -- We may assume `K ≥ 1`.
    set K' : ℝ := max K 1 with hK'def
    have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
    have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le one_pos hK'1
    have hK' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + eps / 2) := by
      intro a b c ha hb hab hsum
      refine le_trans (hK a b c ha hb hab hsum) ?_
      have hr : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + eps / 2) :=
        le_trans zero_le_one (one_le_rad_rpow _ (by linarith))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr
    -- The bound on `c` for exceptional triples.
    set B : ℝ := K' * (K' ^ (2 / eps)) ^ (1 + eps / 2) with hBdef
    refine abcExceptions_finite_of_bounded eps ⌈B⌉₊ ?_
    rintro ⟨a, b, c⟩ ⟨ha, hb, hab, hsum, hex⟩
    simp only at ha hb hab hsum hex ⊢
    set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
    have hr1 : (1 : ℝ) ≤ r := one_le_rad_real _
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
    have hbound := hK' a b c ha hb hab hsum
    have hsplit : r ^ (1 + eps) = r ^ (1 + eps / 2) * r ^ (eps / 2) := by
      rw [← Real.rpow_add hr0]
      ring_nf
    have hpos : (0 : ℝ) < r ^ (1 + eps / 2) := Real.rpow_pos_of_pos hr0 _
    have hlt : r ^ (1 + eps / 2) * r ^ (eps / 2) < K' * r ^ (1 + eps / 2) := by
      calc r ^ (1 + eps / 2) * r ^ (eps / 2) = r ^ (1 + eps) := hsplit.symm
        _ < (c : ℝ) := hex
        _ ≤ K' * r ^ (1 + eps / 2) := hbound
    have hrp : r ^ (eps / 2) < K' := by
      refine lt_of_mul_lt_mul_left (a := r ^ (1 + eps / 2)) ?_ hpos.le
      linarith [hlt]
    have hrle : r ≤ K' ^ (2 / eps) := by
      have h1 : (r ^ (eps / 2)) ^ (2 / eps) ≤ K' ^ (2 / eps) :=
        Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hr0 _)) hrp.le (by positivity)
      have h2 : (r ^ (eps / 2)) ^ (2 / eps) = r := by
        rw [← Real.rpow_mul hr0.le, show eps / 2 * (2 / eps) = 1 by field_simp, Real.rpow_one]
      rwa [h2] at h1
    have hcle : (c : ℝ) ≤ B := by
      refine le_trans hbound ?_
      have h3 : r ^ (1 + eps / 2) ≤ (K' ^ (2 / eps)) ^ (1 + eps / 2) :=
        Real.rpow_le_rpow hr0.le hrle (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hK'0.le
    have : (c : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hcle (Nat.le_ceil B)
    exact_mod_cast this

/-- A sanity check on the radical: `rad (1 * 8 * 9) = 6`. -/
