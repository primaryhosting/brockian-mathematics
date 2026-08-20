/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma mu_mono {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    {F : Finset (Finset α)} (hF : IsUp F) : mu a F ≤ mu c F := by
  rcases eq_or_lt_of_le (le_trans ha0 hac) with h1 | h1
  · -- c = 0, hence a = 0
    have : a = c := by linarith [ha0, hac, h1.symm ▸ hc1]
    rw [this]
  rcases eq_or_lt_of_le hac with h | h
  · rw [h]
  by_cases ha1 : a = 1
  · exfalso; rw [ha1] at h; linarith
  have ha1' : a < 1 := lt_of_le_of_ne (le_trans hac hc1) ha1
  set b : ℝ := (c - a) / (1 - a) with hb
  have h1a : 0 < 1 - a := by linarith
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (le_of_lt h1a)
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one h1a]; linarith
  have hcalc : a + b - a * b = c := by
    rw [hb]
    field_simp
    ring
  have := mu_le_mu_union (α := α) ha0 (le_of_lt ha1') hb0 hb1 hF
  rwa [hcalc] at this

/-- `U` is a cover of the hypergraph `H`. -/
