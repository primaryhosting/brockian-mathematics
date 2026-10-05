import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

lemma eventually_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (3 : ℝ) * ((lowExp n).card : ℝ) ≤ ε * 3 ^ n := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (343 / 432 : ℝ)) (by norm_num) (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε ^ 3 / 27) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall : (343 / 432 : ℝ) ^ n ≤ ε ^ 3 / 27 := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    linarith
  have hcube := lowExp_card_cube_le n
  have hkey : (3 * ((lowExp n).card : ℝ)) ^ 3 ≤ (ε * 3 ^ n) ^ 3 := by
    have h1 : (3 * ((lowExp n).card : ℝ)) ^ 3 = 27 * ((lowExp n).card : ℝ) ^ 3 := by ring
    have h2 : (ε * 3 ^ n) ^ 3 = ε ^ 3 * 27 ^ n := by
      rw [mul_pow, ← pow_mul, mul_comm n 3, pow_mul]
      norm_num
    have h3 : (27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n = (343 / 16 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    have h27 : (0 : ℝ) < (27 : ℝ) ^ n := by positivity
    have h4 : 27 * ((lowExp n).card : ℝ) ^ 3 ≤ 27 * (343 / 16 : ℝ) ^ n := by linarith
    have h5 : (27 : ℝ) * (343 / 16 : ℝ) ^ n ≤ ε ^ 3 * 27 ^ n := by
      rw [← h3]
      have : (27 : ℝ) * ((27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n)
          ≤ 27 * ((27 : ℝ) ^ n * (ε ^ 3 / 27)) := by
        have := mul_le_mul_of_nonneg_left hsmall (le_of_lt h27)
        linarith
      calc (27 : ℝ) * ((27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n)
          ≤ 27 * ((27 : ℝ) ^ n * (ε ^ 3 / 27)) := this
        _ = ε ^ 3 * 27 ^ n := by ring
    rw [h1, h2]
    linarith
  have hnn : (0 : ℝ) ≤ ε * 3 ^ n := by positivity
  exact le_of_pow_le_pow_left₀ (by norm_num) hnn hkey

end CapSetAux

namespace Math2

open CapSetAux

/-- **The cap-set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt).

Subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression have size `o(3ⁿ)`:
for every `ε > 0` there is an `N` such that for all `n ≥ N`, every 3AP-free subset `A`
of `(ZMod 3)ⁿ` satisfies `|A| ≤ ε · 3ⁿ`. -/
