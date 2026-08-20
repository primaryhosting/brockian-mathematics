import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem real_scaled_power_boundary_five_halves {x : ℝ} (hx_large : (4840 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) < ((5 : ℝ) / 4) ^ x := by
  let f : ℝ → ℝ :=
    fun x => log x + √(((5 : ℝ) / 2 * x)) * log (((5 : ℝ) / 2 * x)) -
      log ((5 : ℝ) / 4) * x
  have hf_pos :
      ∀ x, 0 < x →
        0 < x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) /
          ((5 : ℝ) / 4) ^ x := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    exact div_pos (mul_pos hx (rpow_pos_of_pos hbase _)) (rpow_pos_of_pos (by norm_num) _)
  have hf :
      ∀ x, 0 < x →
        f x =
          log (x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) /
            ((5 : ℝ) / 4) ^ x) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    have hrpow : 0 < ((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x)) :=
      rpow_pos_of_pos hbase _
    rw [log_div (mul_pos hx hrpow).ne' (rpow_pos_of_pos (by norm_num) _).ne',
      log_mul hx.ne' hrpow.ne', log_rpow hbase, log_rpow (by norm_num : (0 : ℝ) < 5 / 4)]
    ring
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  rw [← div_lt_one (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 4) x),
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
      · exact (log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 4))
      · exact convexOn_id (convex_Ioi (0.5 : ℝ))
    have hleft : 0.5 < (4410 : ℝ) := by norm_num
    have hx_mem : x ∈ Set.Ioi (0.5 : ℝ) := by exact lt_of_lt_of_le (by norm_num) hx_large
    have hleft_lt_right : (4410 : ℝ) < 4840 := by norm_num
    have hright_le_x : (4840 : ℝ) ≤ x := hx_large
    have hfleft : 0 ≤ f 4410 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4410)) = 105 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_nonneg_iff (hf_pos _ (by norm_num)), hsqrt,
        one_le_div (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4410) : ℝ) = 11025 by norm_num,
        show (105 : ℝ) = (105 : ℕ) by norm_num,
        show (4410 : ℝ) = (4410 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast, div_pow]
      rw [div_le_iff₀ (by positivity)]
      have hcoef : (5 : ℝ) ^ (5 : ℕ) < 4410 := by norm_num
      have hmid : (5 : ℝ) ^ (607 : ℕ) < 11025 ^ (105 : ℕ) := by
        have h₁ : (5 : ℝ) ^ (133 : ℕ) < 11025 ^ (23 : ℕ) := by norm_num
        have h₂ : (5 : ℝ) ^ (75 : ℕ) < 11025 ^ (13 : ℕ) := by norm_num
        calc
          (5 : ℝ) ^ (607 : ℕ) = ((5 : ℝ) ^ (133 : ℕ)) ^ (4 : ℕ) * 5 ^ (75 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (11025 ^ (23 : ℕ)) ^ (4 : ℕ) * 11025 ^ (13 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (4 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 11025 ^ (105 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      have hfour : (5 : ℝ) ^ (3798 : ℕ) < 4 ^ (4410 : ℕ) := by
        have h₁ : (5 : ℝ) ^ (149 : ℕ) < 4 ^ (173 : ℕ) := by norm_num
        have h₂ : (5 : ℝ) ^ (73 : ℕ) < 4 ^ (85 : ℕ) := by norm_num
        calc
          (5 : ℝ) ^ (3798 : ℕ) = ((5 : ℝ) ^ (149 : ℕ)) ^ (25 : ℕ) * 5 ^ (73 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (4 ^ (173 : ℕ)) ^ (25 : ℕ) * 4 ^ (85 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (25 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 4 ^ (4410 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      have hprod :
          (5 : ℝ) ^ (4410 : ℕ) < 4410 * 11025 ^ (105 : ℕ) * 4 ^ (4410 : ℕ) := by
        calc
          (5 : ℝ) ^ (4410 : ℕ) =
              (5 ^ (5 : ℕ) * 5 ^ (607 : ℕ)) * 5 ^ (3798 : ℕ) := by
            rw [← pow_add, ← pow_add]
          _ < (4410 * 11025 ^ (105 : ℕ)) * 4 ^ (4410 : ℕ) :=
            mul_lt_mul
              (mul_lt_mul hcoef hmid.le (by positivity) (by positivity))
              hfour.le (by positivity) (by positivity)
          _ = 4410 * 11025 ^ (105 : ℕ) * 4 ^ (4410 : ℕ) := by rfl
      exact hprod.le
    have hfright : f 4840 < 0 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4840)) = 110 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_neg_iff (hf_pos _ (by norm_num)), hsqrt,
        div_lt_one (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4840) : ℝ) = 12100 by norm_num,
        show (110 : ℝ) = (110 : ℕ) by norm_num,
        show (4840 : ℝ) = (4840 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast, div_pow]
      rw [lt_div_iff₀ (by positivity)]
      have hcoef : (4840 : ℝ) < 5 ^ (6 : ℕ) := by norm_num
      have hmid : (12100 : ℝ) ^ (110 : ℕ) < 5 ^ (660 : ℕ) := by
        calc
          (12100 : ℝ) ^ (110 : ℕ) < (5 ^ (6 : ℕ) : ℝ) ^ (110 : ℕ) :=
            pow_lt_pow_left₀ (by norm_num : (12100 : ℝ) < 5 ^ (6 : ℕ))
              (by positivity) (by norm_num : (110 : ℕ) ≠ 0)
          _ = 5 ^ (660 : ℕ) := by
            rw [← pow_mul]
      have hfour : (4 : ℝ) ^ (4840 : ℕ) < 5 ^ (4173 : ℕ) := by
        have h₁ : (4 : ℝ) ^ (29 : ℕ) < 5 ^ (25 : ℕ) := by norm_num
        have h₂ : (4 : ℝ) ^ (26 : ℕ) < 5 ^ (23 : ℕ) := by norm_num
        calc
          (4 : ℝ) ^ (4840 : ℕ) = ((4 : ℝ) ^ (29 : ℕ)) ^ (166 : ℕ) * 4 ^ (26 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (5 ^ (25 : ℕ)) ^ (166 : ℕ) * 5 ^ (23 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (166 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 5 ^ (4173 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      calc
        (4840 : ℝ) * 12100 ^ (110 : ℕ) * 4 ^ (4840 : ℕ)
            < 5 ^ (6 : ℕ) * 5 ^ (660 : ℕ) * 5 ^ (4173 : ℕ) :=
          mul_lt_mul
            (mul_lt_mul hcoef hmid.le (by positivity) (by positivity))
            hfour.le (by positivity) (by positivity)
        _ = 5 ^ (4839 : ℕ) := by
          rw [← pow_add, ← pow_add]
        _ < 5 ^ (4840 : ℕ) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    have hright_le_left : f 4840 ≤ f 4410 := le_trans (le_of_lt hfright) hfleft
    exact lt_of_le_of_lt
      (hconcave.right_le_of_le_left'' hleft hx_mem hleft_lt_right hright_le_x
        hright_le_left)
      hfright

