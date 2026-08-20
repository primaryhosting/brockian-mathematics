import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma tail_exp_neg_one (n : ℕ) (hn : Even n) :
    ∃ B : ℤ, (n ! : ℝ) * Real.exp (-1) - B < 0 ∧
      -(2 / (n + 1)) ≤ (n ! : ℝ) * Real.exp (-1) - B := by
  obtain ⟨B, hB⟩ := exists_int_einv n
  use B
  have hx : |(-1 : ℝ)| ≤ 1 := by norm_num
  have hkey := tail_key (-1) hx n B hB
  -- Since n is even: (-1)^(n+1) = -1 and (-1)^(n+2) = 1
  have hexp1 : (-1 : ℝ) ^ (n + 1) = -1 := by
    rw [even_iff_two_dvd] at hn
    obtain ⟨k, hk⟩ := hn
    simp [hk, pow_add]
  have hexp2 : (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [even_iff_two_dvd] at hn
    obtain ⟨k, hk⟩ := hn
    simp [hk, pow_add]
  rw [hexp1, hexp2] at hkey
  -- Simplify: -1/(n+1) + 1/((n+1)*(n+2)) = -1/(n+2)
  have hsimplify : -1 * (1 / ((n : ℝ) + 1)) + 1 * (1 / ((n + 1) * (n + 2) : ℝ)) = -1 / (n + 2) := by
    field_simp
    ring
  rw [hsimplify] at hkey
  -- hkey: |δ + 1/(n+2)| ≤ error where δ = n! * e^(-1) - B
  -- So: -error - 1/(n+2) ≤ δ ≤ error - 1/(n+2)
  set δ := (n ! : ℝ) * Real.exp (-1) - B with hδ_def
  set error := (n + 4 : ℝ) / ((n + 1) * (n + 2) * (n + 3) * (n + 3)) with herror_def
  have hneg : δ - -1 / (n + 2 : ℝ) = δ + 1 / (n + 2) := by ring
  have hkey' : -error - 1 / (n + 2) ≤ δ ∧ δ ≤ error - 1 / (n + 2) := by
    have := abs_le.mp hkey
    rw [hneg] at this
    constructor <;> linarith
  -- For δ < 0, need error < 1/(n+2)
  have herror_lt : error < 1 / (n + 2) := by
    rw [herror_def]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n + 1) * (n + 2) * (n + 3) * (n + 3)) (by positivity : (0 : ℝ) < n + 2)]
    ring_nf
    nlinarith [sq_nonneg (n : ℝ)]
  have h1 : δ < 0 := by linarith [hkey'.2, herror_lt]
  -- For -2/(n+1) ≤ δ, need error + 1/(n+2) ≤ 2/(n+1)
  -- num_bound_le: 1/(n+1) + 1/((n+1)*(n+2)) + error ≤ 2/(n+1)
  have h2 : -(2 / (n + 1)) ≤ δ := by
    have hkey'_lower := hkey'.1
    have hbound : -(2 / (n + 1)) ≤ -error - 1 / (n + 2) := by
      rw [herror_def]
      field_simp
      ring_nf
      nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]
    linarith
  exact ⟨h1, h2⟩

/-- e² is irrational. -/
