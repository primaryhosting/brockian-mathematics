import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le_half_add_one (k : ℕ) :
    (k + 1).primesBelow.card ≤ k / 2 + 1 := by
  classical
  let odds : Finset ℕ := (Finset.Icc 1 (k / 2)).image fun t => 2 * t + 1
  have hsubset : (k + 1).primesBelow ⊆ insert 2 odds := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
    by_cases hp_two : p = 2
    · exact Finset.mem_insert.mpr (Or.inl hp_two)
    · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
      have hp_two_le : 2 ≤ p := hp_prime.two_le
      have hp_div_mem : p / 2 ∈ Finset.Icc 1 (k / 2) := by
        rw [Finset.mem_Icc]
        exact ⟨Nat.div_pos hp_two_le (by norm_num),
          Nat.div_le_div_right hp_le_k⟩
      have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
      have hp_mem_odds : p ∈ odds := by
        rw [Finset.mem_image]
        exact ⟨p / 2, hp_div_mem, hp_eq⟩
      exact Finset.mem_insert.mpr (Or.inr hp_mem_odds)
  calc
    (k + 1).primesBelow.card ≤ (insert 2 odds).card := Finset.card_le_card hsubset
    _ ≤ odds.card + 1 := Finset.card_insert_le 2 odds
    _ ≤ (Finset.Icc 1 (k / 2)).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = k / 2 + 1 := by
      rw [Nat.card_Icc]
      omega

