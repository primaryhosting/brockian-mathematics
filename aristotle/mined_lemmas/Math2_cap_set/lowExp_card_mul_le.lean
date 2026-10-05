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

lemma lowExp_card_mul_le (n : ℕ) :
    ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) ≤ (7 / 4) ^ n := by
  have h1 : ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n)
      = ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n)
      ≤ ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hdeg : deg n a ≤ D0 n := by
      simpa [lowExp] using ha
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hdeg
  have h3 : ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) ≤ ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => by positivity)
  rw [h1]
  calc ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n) ≤ ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) := h2
    _ ≤ ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) := h3
    _ = (7 / 4) ^ n := sum_half_pow_deg n

/-- The cube of the number of low-degree exponent vectors is at most `(343/16)ⁿ`. -/
