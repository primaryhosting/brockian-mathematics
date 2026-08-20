import RequestProject.Main

/-!
# Log-concavity of the characteristic polynomial of a uniform matroid

This file constructs the uniform matroid `U_{r,E}` on a finite ground set `E` and proves that
the coefficients of its characteristic polynomial form a log-concave sequence, i.e. the
Adiprasito–Huh–Katz theorem for uniform matroids.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The uniform matroid `U_{r,E}`: the independent sets are the subsets of `E` of size at most
`r`. -/

theorem whitneyAbs_unifOn_zero (E : Finset α) (r : ℕ) (hr : r ≤ E.card) (hr0 : 1 ≤ r) :
    whitneyAbs (unifOn E r) E 0 = (E.card - 1).choose (r - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, E.card = m + 1 := ⟨E.card - 1, by omega⟩
  rw [whitneyAbs, coeff_charPoly_unifOn E (j + 1) 0 hr, hm]
  rw [hm] at hr
  have hsplit : ∑ k ∈ Finset.range (m + 1 + 1),
        ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) * (if 0 = j + 1 - min k (j + 1) then 1 else 0)
      = ∑ k ∈ Finset.Ico (j + 1) (m + 1 + 1), ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total (j + 1) k with h | h
      · exact ⟨h, h1⟩
      · simp [h] at h2; omega
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by simp [min_eq_right h1]⟩
  have htot : ∑ k ∈ Finset.range (m + 1 + 1), ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) = 0 := by
    rw [Int.alternating_sum_range_choose, if_neg (by omega)]
  rw [hsplit, Finset.sum_Ico_eq_sub _ (by omega), htot, alternating_partial_sum m j]
  simp only [Nat.add_sub_cancel, zero_sub]
  rw [Int.natAbs_neg]
  exact natAbs_signed j _

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz), proved
here in the special case of uniform matroids: for the uniform matroid `U_{r,E}` of rank
`1 ≤ r ≤ |E|` on a finite ground set `E`, the absolute values `w_i` of the coefficients of the
characteristic polynomial form a log-concave sequence, `w_i · w_{i+2} ≤ w_{i+1}^2`.
The free (Boolean) matroid is the case `r = |E|` (see `Frontier.freeOn_eq_unifOn`). -/
