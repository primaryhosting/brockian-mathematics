/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem norm_le_one_of_liSumOf_nonneg {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ liSumOf z n) (k : ℕ) :
    ‖z k‖ ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM1, hMex, hMle⟩ := exists_max_norm he hcon
  obtain ⟨F, M', hFne, hFM, hM'1, hM'M, hout⟩ := exists_gap he hM1 hMle hMex
  set T : ℝ := ∑' k, liMajorant z k with hT
  have hT0 : 0 ≤ T := tsum_nonneg (liMajorant_nonneg z)
  have hM0 : (0 : ℝ) < M := by linarith
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hcard1 : (1 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hFne
  have hlim : Tendsto (fun n : ℕ =>
      (F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (F.card : ℝ) * (M⁻¹) ^ n) atTop (nhds 0) := by
      have hb : |M⁻¹| < 1 := by
        rw [abs_of_pos (by positivity), inv_lt_one_iff₀]
        exact Or.inr hM1
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).const_mul ((F.card : ℝ))
    have h2 : Tendsto (fun n : ℕ => 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) atTop (nhds 0) := by
      have hb : |M' / M| < 1 := by
        rw [abs_of_nonneg (by positivity), div_lt_one hM0]
        exact hM'M
      simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hb).const_mul (2 * T)
    simpa using h1.add h2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  have hwunit : ∀ j ∈ F, ‖z j / (M : ℂ)‖ = 1 := by
    intro j hj
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, hFM j hj, div_self hM0.ne']
  obtain ⟨n, hnN, hn1, hrec⟩ :=
    simultaneous_recurrence F (fun j => z j / (M : ℂ)) hwunit 1 one_pos N
  have hFbound : ∀ j ∈ F, (1 - (z j) ^ n).re ≤ 1 - M ^ n / 2 := by
    intro j hj
    have hu : ‖(z j / (M : ℂ))‖ = 1 := hwunit j hj
    have hun : ‖(z j / (M : ℂ)) ^ n‖ = 1 := by rw [norm_pow, hu, one_pow]
    have hrecj := hrec j hj
    set v : ℂ := (z j / (M : ℂ)) ^ n with hv
    have hre : (1 : ℝ) / 2 ≤ v.re := by
      have h2 : ‖v - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (v - 1)]
      rw [Complex.sq_norm] at h2
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero] at h2
      have h3 : Complex.normSq v = 1 := by
        have := Complex.sq_norm v; rw [hun] at this; simpa using this.symm
      simp only [Complex.normSq_apply] at h3
      nlinarith
    have hzj : (z j) ^ n = (M : ℂ) ^ n * v := by
      rw [hv, div_pow]; field_simp
    have hzre : ((z j) ^ n).re = M ^ n * v.re := by
      rw [hzj, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.one_re, hzre]
    have hMn : (0 : ℝ) < M ^ n := pow_pos hM0 n
    nlinarith
  have hsum := (summable_liTerms hd he n).sum_add_tsum_compl (s := F)
  have htail := tail_bound hd he F M' hM'1 hout n hn1
  have hFsum : ∑ j ∈ F, (1 - (z j) ^ n).re ≤ (F.card : ℝ) * (1 - M ^ n / 2) := by
    calc ∑ j ∈ F, (1 - (z j) ^ n).re ≤ ∑ _j ∈ F, (1 - M ^ n / 2) := Finset.sum_le_sum hFbound
    _ = (F.card : ℝ) * (1 - M ^ n / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpos := h n hn1
  rw [liSumOf, ← hsum] at hpos
  have hMn : (0 : ℝ) < M ^ n := pow_pos hM0 n
  have hkey := hN n hnN
  have hmul : ((F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) * M ^ n
      = (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T := by
    have h1 : (M⁻¹) ^ n * M ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hM0.ne', one_pow]
    have h2 : (M' / M) ^ n * M ^ n = M' ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hM0.ne')]
    calc ((F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) * M ^ n
        = (F.card : ℝ) * ((M⁻¹) ^ n * M ^ n)
          + 2 * T * (n : ℝ) ^ 2 * ((M' / M) ^ n * M ^ n) := by ring
    _ = (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T := by rw [h1, h2]; ring
  have hfinal : (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T < M ^ n / 2 := by
    have h4 := mul_lt_mul_of_pos_right hkey hMn
    rw [hmul] at h4
    calc (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T < 1 / 2 * M ^ n := h4
    _ = M ^ n / 2 := by ring
  have hcardM : (F.card : ℝ) * (1 - M ^ n / 2) ≤ (F.card : ℝ) - M ^ n / 2 := by nlinarith
  linarith

/-- **Abstract positivity criterion** (the analytic core of Li's criterion, in the spirit of
Bombieri--Lagarias): under the two summability hypotheses, all Li sums of the family are
nonnegative if and only if every member of the family lies in the closed unit disc. -/
