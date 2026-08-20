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

theorem huh_matroid_log_concave (E : Finset α) (r : ℕ) (hr : r ≤ E.card) (hr0 : 1 ≤ r)
    (i : ℕ) :
    whitneyAbs (unifOn E r) E i * whitneyAbs (unifOn E r) E (i + 2)
      ≤ whitneyAbs (unifOn E r) E (i + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [whitneyAbs_unifOn_zero E r hr hr0, whitneyAbs_unifOn_pos E r 1 hr le_rfl,
      whitneyAbs_unifOn_pos E r 2 hr (by omega)]
    rcases lt_or_ge r 2 with h2 | h2
    · rw [if_neg (by omega), mul_zero]
      exact Nat.zero_le _
    · rw [if_pos (by omega), if_pos (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, E.card = m + 1 := ⟨E.card - 1, by omega⟩
      have hle : (E.card - 1).choose (k + 1) ≤ E.card.choose (k + 2) := by
        rw [hm, Nat.add_sub_cancel, Nat.choose_succ_succ' m (k + 1)]
        omega
      have s1 : k + 2 - 1 = k + 1 := by omega
      have s2 : k + 2 - 2 = k := by omega
      rw [s1, s2]
      calc (E.card - 1).choose (k + 1) * E.card.choose k
          ≤ E.card.choose (k + 2) * E.card.choose k := Nat.mul_le_mul_right _ hle
        _ = E.card.choose k * E.card.choose (k + 2) := Nat.mul_comm _ _
        _ ≤ E.card.choose (k + 1) ^ 2 := by
            rw [pow_two]; exact choose_log_concave E.card k
  · rw [whitneyAbs_unifOn_pos E r i hr hi, whitneyAbs_unifOn_pos E r (i + 1) hr (by omega),
      whitneyAbs_unifOn_pos E r (i + 2) hr (by omega)]
    rcases le_or_gt (i + 2) r with h | h
    · rw [if_pos h, if_pos (by omega), if_pos (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, r - i = k + 2 := ⟨r - i - 2, by omega⟩
      have e1 : r - (i + 1) = k + 1 := by omega
      have e2 : r - (i + 2) = k := by omega
      rw [hk, e1, e2, pow_two, Nat.mul_comm]
      exact choose_log_concave E.card k
    · rw [if_neg (show ¬ (i + 2 ≤ r) by omega), mul_zero]
      exact Nat.zero_le _

/-- The free matroid on `E` is the uniform matroid of rank `|E|` on `E`. -/
