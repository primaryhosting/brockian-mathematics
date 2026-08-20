import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

theorem exp_two_irrational : Irrational (Real.exp 2) := by
  -- Key insight: e² = (n! * e) / (n! * e^{-1})
  -- If e² = p/q, then q * (n! * e) = p * (n! * e^{-1})
  -- This leads to pB - qA = qδ₁ + pδ₂ where δ₁, δ₂ are small
  -- For large n, qδ₁ + pδ₂ < 1, but pB - qA is a positive integer, contradiction!
  by_contra h
  rw [Irrational] at h
  push_neg at h
  obtain ⟨r, hr⟩ := h
  -- We'll use n = 2 * (|p| + q) to ensure n is even and large enough
  -- First, establish that r > 0 so p > 0
  have hr_pos : (r : ℝ) > 0 := by rw [hr]; exact Real.exp_pos 2
  have hr_pos_rat : r > 0 := by contrapose! hr_pos; exact mod_cast hr_pos
  have hp_pos' : r.num > 0 := Rat.num_pos.mpr hr_pos_rat
  -- Use n = 2 * (|p| + q) to ensure n is even and large enough
  set n := 2 * (r.num.natAbs + r.den) with hn_def
  have hn_even : Even n := even_two_mul _
  have hq_pos : 0 < r.den := r.pos
  -- Get bounds on n! * e and n! * e^{-1}
  obtain ⟨A, hA_pos, hA_bound⟩ := tail_exp_one n
  obtain ⟨B, hB_neg, hB_bound⟩ := tail_exp_neg_one n hn_even
  -- n! * e = A + δ₁ where 0 < δ₁ ≤ 2/(n+1)
  set δ₁ := (n ! : ℝ) * Real.exp 1 - A with hδ₁_def
  have hδ₁_pos : 0 < δ₁ := hA_pos
  have hδ₁_bound : δ₁ ≤ 2 / (n + 1) := hA_bound
  -- n! * e^{-1} = B - δ₂ where 0 < δ₂ ≤ 2/(n+1)
  set δ₂ := B - (n ! : ℝ) * Real.exp (-1) with hδ₂_def
  have hδ₂_pos : 0 < δ₂ := by linarith
  have hδ₂_bound : δ₂ ≤ 2 / (n + 1) := by linarith
  -- e² = (n! * e) / (n! * e^{-1}) = (A + δ₁) / (B - δ₂)
  have he2_eq : Real.exp 2 = Real.exp 1 / Real.exp (-1) := by
    rw [← Real.exp_sub]; norm_num
  have hexp_ratio : Real.exp 2 = ((n ! : ℝ) * Real.exp 1) / ((n ! : ℝ) * Real.exp (-1)) := by
    rw [mul_div_mul_left _ _ (by positivity : (n ! : ℝ) ≠ 0)]
    exact he2_eq
  -- Let X = n! * e = A + δ₁ and Y = n! * e^{-1} = B - δ₂
  set X := (n ! : ℝ) * Real.exp 1 with hX_def
  set Y := (n ! : ℝ) * Real.exp (-1) with hY_def
  have hX_eq : X = A + δ₁ := by rw [hδ₁_def]; ring
  have hY_eq : Y = B - δ₂ := by rw [hδ₂_def]; ring
  -- If e² = r = p/q, then X / Y = r, so X = r * Y
  -- This means q * X = p * Y, so q(A + δ₁) = p(B - δ₂)
  -- Therefore pB - qA = qδ₁ + pδ₂ > 0
  have hr_eq_exp2 : (r : ℝ) = Real.exp 2 := hr
  have hXY_ne_zero : Y ≠ 0 := by simp [hY_def]; positivity
  have hXY_ratio : X / Y = r := by rw [← hexp_ratio, hr_eq_exp2]
  have hqX_eq_pY : (r.den : ℝ) * X = r.num * Y := by
    have h1 : X = r * Y := by field_simp [hXY_ne_zero] at hXY_ratio ⊢; linarith
    calc (r.den : ℝ) * X = r.den * (r * Y) := by rw [h1]
      _ = (r.den * r) * Y := by ring
      _ = r.num * Y := by rw [show (r.den : ℝ) * r = r.num from by simp [Rat.cast_def]; field_simp]
  -- pB - qA = qδ₁ + pδ₂
  set p := r.num with hp_def
  set q := r.den with hq_def
  have hpB_qA : (p : ℝ) * B - (q : ℝ) * A = (q : ℝ) * δ₁ + (p : ℝ) * δ₂ := by
    rw [hX_eq, hY_eq] at hqX_eq_pY
    linarith
  -- p > 0 since r = exp(2) > 0
  have hp_pos : p > 0 := hp_pos'
  -- pB - qA > 0
  have hpB_qA_pos : (p : ℝ) * B - (q : ℝ) * A > 0 := by
    rw [hpB_qA]
    have hp_pos_real : (p : ℝ) > 0 := mod_cast hp_pos
    have hq_pos_real : (q : ℝ) > 0 := mod_cast hq_pos
    nlinarith [hδ₁_pos, hδ₂_pos]
  -- But q * δ₁ + p * δ₂ < 1 for our choice of n
  -- The sum q * δ₁ + p * δ₂ ≤ (p + q) * 2 / (n + 1)
  have hsum_bound : (q : ℝ) * δ₁ + (p : ℝ) * δ₂ ≤ ((p.natAbs : ℝ) + q) * 2 / (n + 1) := by
    have hp_pos_real : (p : ℝ) = (p.natAbs : ℝ) := by
      simp [abs_of_pos (by exact_mod_cast hp_pos : (p : ℝ) > 0)]
    rw [hp_pos_real]
    have h1 : (q : ℝ) * δ₁ + (p.natAbs : ℝ) * δ₂ ≤ (q : ℝ) * (2 / (n + 1)) + (p.natAbs : ℝ) * (2 / (n + 1)) := by
      nlinarith [hδ₁_bound, hδ₂_bound]
    have h2 : (q : ℝ) * (2 / (n + 1)) + (p.natAbs : ℝ) * (2 / (n + 1)) = ((p.natAbs : ℝ) + q) * 2 / (n + 1) := by ring
    linarith
  -- With n = 2 * (p.natAbs + q), we have (p.natAbs + q) * 2 / (n + 1) < 1
  have hlt_one : ((p.natAbs : ℝ) + q) * 2 / (n + 1) < 1 := by
    rw [hn_def]
    have hpq_pos : (p.natAbs : ℝ) + q > 0 := by positivity
    rw [div_lt_one (by linarith : (n : ℝ) + 1 > 0)]
    rw [hn_def]
    norm_cast
    linarith
  -- Therefore p * B - q * A < 1
  have hpbqa_lt_one : (p : ℝ) * B - (q : ℝ) * A < 1 := by linarith [hsum_bound, hlt_one]
  -- But p * B - q * A is a positive integer, so ≥ 1, contradiction!
  have hpbqa_int : ∃ m : ℤ, (p : ℝ) * B - (q : ℝ) * A = m := ⟨p * B - q * A, by push_cast; ring⟩
  obtain ⟨m, hm⟩ := hpbqa_int
  have hm_pos : m > 0 := Int.cast_pos.mp (hm ▸ hpB_qA_pos)
  have hm_ge_one : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
  linarith

end Brockian.MsE2Irrational

