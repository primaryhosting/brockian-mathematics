import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma exp_err (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.exp x - ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)|
      ≤ ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
  have key : Real.exp x = ∑' i, x ^ i / (i ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div x
  rw [key]
  -- Need to bound the tail of the exponential series
  have hs := Real.summable_pow_div_factorial x
  rw [← hs.sum_add_tsum_nat_add (k := n + 3)]
  ring_nf
  -- Goal is now in a complicated form; simplify it first
  have hrhs : (n : ℝ) * ((n : ℝ) * ((3 + n)! : ℝ) + ((3 + n)! : ℝ) * 3)⁻¹ +
              ((n : ℝ) * ((3 + n)! : ℝ) + ((3 + n)! : ℝ) * 3)⁻¹ * 4 =
              ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
    field_simp
    ring_nf
  rw [hrhs]
  -- Need to show |∑' i, x^(3+n+i) / (3+n+i)!| ≤ (n+4) / ((n+3)! * (n+3))
  have hsumm : Summable (fun i => x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)) := by
    exact Real.summable_pow_div_factorial x |>.comp_injective (add_left_injective (n + 3))
  have heq : ∀ i : ℕ, x ^ 3 * x ^ n * x ^ i * ((3 + n + i)! : ℝ)⁻¹ = x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
    intro i
    ring_nf
  simp_rw [heq]
  calc |∑' (i : ℕ), x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)|
      ≤ ∑' (i : ℕ), |x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)| := by
        simp only [← Real.norm_eq_abs]
        apply norm_tsum_le_tsum_norm
        exact hsumm.norm
      _ = ∑' (i : ℕ), |x| ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
        congr 1
        ext i
        rw [abs_div, abs_pow]
        rw [abs_of_pos (by positivity : (0 : ℝ) < ((i + (n + 3))! : ℝ))]
      _ ≤ ∑' (i : ℕ), (1 : ℝ) ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
        apply Summable.tsum_le_tsum
        · intro i
          gcongr
        · exact Real.summable_pow_div_factorial |x| |>.comp_injective (add_left_injective (n + 3))
        · exact Real.summable_pow_div_factorial 1 |>.comp_injective (add_left_injective (n + 3))
      _ = ∑' (i : ℕ), ((i + (n + 3))! : ℝ)⁻¹ := by simp
      _ ≤ ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
        -- Each term 1/(n+3+i)! ≤ 1/((n+3)! * (n+4)^i)
        -- So the sum is ≤ 1/(n+3)! * ∑_{i=0}^∞ (1/(n+4))^i = 1/(n+3)! * (n+4)/(n+3)
        have hfact_bound : ∀ i : ℕ, ((i + (n + 3))! : ℝ) ≥ ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i) := by
          intro i
          induction i with
          | zero => simp
          | succ i ih =>
            have step1 : ((i + 1) + (n + 3))! = (i + 1 + (n + 3)) * (i + (n + 3))! := by
              rw [Nat.add_right_comm, Nat.factorial_succ]
            have step2 : ((i + 1) + (n + 3)) ≥ (n + 4) := by omega
            have step3 : ((i + 1 + (n + 3)) : ℝ) ≥ (n + 4) := by exact_mod_cast step2
            calc (((i + 1) + (n + 3))! : ℝ) = ((i + 1 + (n + 3)) : ℝ) * ((i + (n + 3))! : ℝ) := by
                  rw [step1]; push_cast; ring
              _ ≥ (n + 4) * ((i + (n + 3))! : ℝ) := by gcongr
              _ ≥ (n + 4) * (((n + 3)! : ℝ) * (n + 4 : ℝ) ^ i) := by gcongr
              _ = ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ (i + 1)) := by ring
        have hbound : ∀ i : ℕ, ((i + (n + 3))! : ℝ)⁻¹ ≤ ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i := by
          intro i
          have hfact := hfact_bound i
          have hrhs_eq : ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i =
              (((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i))⁻¹ := by
            rw [mul_inv, inv_pow]
          rw [hrhs_eq]
          exact inv_le_inv₀ (by positivity : (0 : ℝ) < ((i + (n + 3))! : ℝ))
                           (by positivity : (0 : ℝ) < ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i)) |>.mpr hfact
        -- Sum the geometric series
        have hinv_lt_one : (n + 4 : ℝ)⁻¹ < 1 := by
          rw [inv_lt_one₀]
          · linarith
          · linarith
        have hgeom_summable : Summable (fun i : ℕ => ((n + 4 : ℝ)⁻¹) ^ i) :=
          summable_geometric_of_lt_one (by positivity) hinv_lt_one
        have hsum_bound : ∑' i : ℕ, ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i =
            ((n + 3)! : ℝ)⁻¹ * ((n + 4) / (n + 3)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv_lt_one]
          have hpos : (n : ℝ) + 3 ≠ 0 := by linarith
          have hpos2 : (1 - (n + 4 : ℝ)⁻¹) ≠ 0 := by
            have : (n + 4 : ℝ)⁻¹ < 1 := hinv_lt_one
            linarith
          have heq2 : (1 - (n + 4 : ℝ)⁻¹)⁻¹ = (n + 4) / (n + 3) := by
            have h1 : (1 - (n + 4 : ℝ)⁻¹) = ((n + 3) : ℝ) / (n + 4) := by
              field_simp
              ring
            rw [h1]
            field_simp
          rw [heq2]
        have hfinal : ((n + 3)! : ℝ)⁻¹ * ((n + 4) / (n + 3)) = (n + 4) / ((n + 3)! * (n + 3)) := by
          field_simp
        rw [hfinal] at hsum_bound
        have hsumm2 : Summable (fun i => ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i) :=
          hgeom_summable.mul_left _
        have hsumm1 : Summable (fun i => ((i + (n + 3))! : ℝ)⁻¹) := by
          have := Real.summable_pow_div_factorial (1 : ℝ) |>.comp_injective (add_left_injective (n + 3))
          simp only [one_pow] at this
          simp only [one_div] at this
          exact this
        exact le_trans (Summable.tsum_le_tsum hbound hsumm1 hsumm2) hsum_bound.le

/-- Rewriting `n !` times the partial sum of length `n + 3`. -/
