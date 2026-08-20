import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/

private lemma prod_le_two_mul_prod_pred {S : Finset ℕ} (hS : S.card ≤ 2)
    (h3 : ∀ p ∈ S, 3 ≤ p) : (∏ p ∈ S, p) ≤ 2 * ∏ p ∈ S, (p - 1) := by
  by_cases hc : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS]
  · by_cases hc1 : S.card = 1
    · rcases Finset.card_eq_one.mp hc1 with ⟨p, hp⟩
      subst hp
      simp only [Finset.prod_singleton]
      have := h3 p (Finset.mem_singleton_self p)
      omega
    · have hc2 : S.card = 2 := by omega
      rcases Finset.card_eq_two.mp hc2 with ⟨a, b, hab, rfl⟩
      have ha : 3 ≤ a := h3 a (by simp)
      have hb : 3 ≤ b := h3 b (by simp)
      rw [Finset.prod_pair hab, Finset.prod_pair hab]
      obtain ⟨x, rfl⟩ : ∃ x, a = x + 3 := ⟨a - 3, by omega⟩
      obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
      have e1 : x + 3 - 1 = x + 2 := by omega
      have e2 : y + 3 - 1 = y + 2 := by omega
      rw [e1, e2]
      have hxy : 1 ≤ x + y := by
        rcases Nat.eq_zero_or_pos x with hx | hx
        · subst hx
          have : y ≠ 0 := by rintro rfl; exact hab rfl
          omega
        · omega
      nlinarith [hxy]

/-- An odd perfect number has at least three distinct prime factors. -/
