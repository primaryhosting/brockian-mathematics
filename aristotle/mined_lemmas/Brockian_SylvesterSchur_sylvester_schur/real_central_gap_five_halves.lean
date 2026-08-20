import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem real_central_gap_five_halves {x : ℝ} (hx_large : (4410 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) *
        4 ^ (((5 : ℝ) / 2 * x) / 3) < 4 ^ x := by
  let f : ℝ → ℝ :=
    fun x => log x + √(((5 : ℝ) / 2 * x)) * log (((5 : ℝ) / 2 * x)) -
      log 4 / 6 * x
  have hf_pos :
      ∀ x, 0 < x →
        0 < x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) / 4 ^ (x / 6) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    exact div_pos (mul_pos hx (rpow_pos_of_pos hbase _)) (rpow_pos_of_pos four_pos _)
  have hf :
      ∀ x, 0 < x →
        f x =
          log (x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) / 4 ^ (x / 6)) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    have hrpow : 0 < ((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x)) :=
      rpow_pos_of_pos hbase _
    rw [log_div (mul_pos hx hrpow).ne' (rpow_pos_of_pos four_pos _).ne',
      log_mul hx.ne' hrpow.ne', log_rpow hbase, log_rpow zero_lt_four]
    ring
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  rw [← div_lt_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div,
    ← rpow_sub four_pos, show x - (5 / 2 * x) / 3 = x / 6 by ring,
    ← log_neg_iff (hf_pos x hx_pos), ← hf x hx_pos]
  · have hconcave : ConcaveOn ℝ (Set.Ioi 0.5) f := by
      apply ConcaveOn.sub
      · apply ConcaveOn.add
        · exact strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
        exact ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
          (((5 : ℝ) / 2) • LinearMap.id)).subset
            (fun y hy => by
              rw [Set.mem_Ioi] at hy
              simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
                LinearMap.id_coe, id_eq, smul_eq_mul]
              nlinarith [hy])
            (convex_Ioi 0.5))
      apply ConvexOn.smul
      · refine div_nonneg (log_nonneg (by norm_num)) (by norm_num)
      · exact convexOn_id (convex_Ioi (0.5 : ℝ))
    have hleft : 0.5 < (3240 : ℝ) := by norm_num
    have hx_mem : x ∈ Set.Ioi (0.5 : ℝ) := by exact lt_of_lt_of_le (by norm_num) hx_large
    have hleft_lt_right : (3240 : ℝ) < 4410 := by norm_num
    have hright_le_x : (4410 : ℝ) ≤ x := hx_large
    have hfleft : 0 ≤ f 3240 := by
      have hsqrt : √(((5 : ℝ) / 2 * 3240)) = 90 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_nonneg_iff (hf_pos _ (by norm_num)), hsqrt,
        one_le_div (by positivity)]
      rw [show (((5 : ℝ) / 2 * 3240) : ℝ) = 8100 by norm_num,
        show (90 : ℝ) = (90 : ℕ) by norm_num,
        show (3240 / 6 : ℝ) = (540 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      have hpow : (4 : ℝ) ^ (540 : ℕ) < (8100 : ℝ) ^ (90 : ℕ) := by
        calc
          (4 : ℝ) ^ (540 : ℕ) = 2 ^ (1080 : ℕ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
          _ = ((2 : ℝ) ^ (12 : ℕ)) ^ (90 : ℕ) := by
            rw [← pow_mul]
          _ < (8100 : ℝ) ^ (90 : ℕ) :=
            pow_lt_pow_left₀ (by norm_num : (2 : ℝ) ^ (12 : ℕ) < 8100)
              (by positivity)
              (by norm_num : (90 : ℕ) ≠ 0)
      exact hpow.le.trans (by
        have hpos : 0 < (8100 : ℝ) ^ (90 : ℕ) :=
          pow_pos (by norm_num : (0 : ℝ) < 8100) (90 : ℕ)
        nlinarith)
    have hfright : f 4410 < 0 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4410)) = 105 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_neg_iff (hf_pos _ (by norm_num)), hsqrt,
        div_lt_one (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4410) : ℝ) = 11025 by norm_num,
        show (105 : ℝ) = (105 : ℕ) by norm_num,
        show (4410 / 6 : ℝ) = (735 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      have hbase : (11025 : ℝ) ^ (3 : ℕ) < 2 ^ (41 : ℕ) := by norm_num
      have hcoef : (4410 : ℝ) < 2 ^ (13 : ℕ) := by norm_num
      have hpow :
          (11025 : ℝ) ^ (105 : ℕ) < 2 ^ (1435 : ℕ) := by
        calc
          (11025 : ℝ) ^ (105 : ℕ) = ((11025 : ℝ) ^ (3 : ℕ)) ^ (35 : ℕ) := by
            norm_num [pow_mul]
          _ < (2 ^ (41 : ℕ) : ℝ) ^ (35 : ℕ) :=
            pow_lt_pow_left₀ hbase (by positivity) (by norm_num : (35 : ℕ) ≠ 0)
          _ = 2 ^ (1435 : ℕ) := by
            rw [← pow_mul]
      calc
        (4410 : ℝ) * 11025 ^ (105 : ℕ) < 2 ^ (13 : ℕ) * 2 ^ (1435 : ℕ) :=
          mul_lt_mul hcoef hpow.le (pow_pos (by norm_num : (0 : ℝ) < 11025) (105 : ℕ))
            (by positivity)
        _ = 2 ^ (1448 : ℕ) := by
          rw [← pow_add]
        _ < 2 ^ (1470 : ℕ) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
        _ = 4 ^ (735 : ℕ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    have hright_le_left : f 4410 ≤ f 3240 := le_trans (le_of_lt hfright) hfleft
    exact lt_of_le_of_lt
      (hconcave.right_le_of_le_left'' hleft hx_mem hleft_lt_right hright_le_x
        hright_le_left)
      hfright

