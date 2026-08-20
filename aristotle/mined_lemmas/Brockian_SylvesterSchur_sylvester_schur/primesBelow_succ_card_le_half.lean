import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le_half {k : ℕ} (hk : 8 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 2 := by
  classical
  rcases k.even_or_odd with heven | hodd
  · obtain ⟨a, rfl⟩ := heven
    have ha : 4 ≤ a := by omega
    let odds : Finset ℕ := (Finset.Icc 1 (a - 1)).image fun t => 2 * t + 1
    have hsubset : (a + a + 1).primesBelow ⊆ insert 2 odds := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
      have hp_le : p ≤ a + a := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
        have hp_two_le : 2 ≤ p := hp_prime.two_le
        have hp_lt : p < a + a := by
          have hp_ne : p ≠ a + a := by
            intro h
            have h_even : Even p := h.symm ▸ (show Even (a + a) from ⟨a, rfl⟩)
            exact (Nat.not_even_iff_odd.mpr hp_odd) h_even
          omega
        have hp_div_mem : p / 2 ∈ Finset.Icc 1 (a - 1) := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hp_two_le (by norm_num)
          · have hdiv_lt : p / 2 < a := by
              have hp_lt' : p < a * 2 := by omega
              exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mpr hp_lt'
            omega
        have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
        have hp_mem_odds : p ∈ odds := by
          rw [Finset.mem_image]
          exact ⟨p / 2, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr (Or.inr hp_mem_odds)
    calc
      (a + a + 1).primesBelow.card ≤ (insert 2 odds).card := Finset.card_le_card hsubset
      _ ≤ odds.card + 1 := Finset.card_insert_le 2 odds
      _ ≤ (Finset.Icc 1 (a - 1)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
      _ = a := by
        rw [Nat.card_Icc]
        omega
      _ = (a + a) / 2 := by omega
  · obtain ⟨a, rfl⟩ := hodd
    have ha : 4 ≤ a := by omega
    let odds : Finset ℕ := (Finset.Icc 1 a).image fun t => 2 * t + 1
    have h9_mem : 9 ∈ odds := by
      rw [Finset.mem_image]
      refine ⟨4, ?_, by norm_num⟩
      rw [Finset.mem_Icc]
      omega
    have hsubset : (2 * a + 1 + 1).primesBelow ⊆ insert 2 (odds.erase 9) := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
      have hp_le : p ≤ 2 * a + 1 := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
        have hp_two_le : 2 ≤ p := hp_prime.two_le
        have hp_div_mem : p / 2 ∈ Finset.Icc 1 a := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hp_two_le (by norm_num)
          · have hdiv_le : p / 2 ≤ (2 * a + 1) / 2 := Nat.div_le_div_right hp_le
            omega
        have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
        have hp_mem_odds : p ∈ odds := by
          rw [Finset.mem_image]
          exact ⟨p / 2, hp_div_mem, hp_eq⟩
        have hp_ne9 : p ≠ 9 := by
          intro h
          subst h
          norm_num at hp_prime
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hp_ne9, hp_mem_odds⟩))
    calc
      (2 * a + 1 + 1).primesBelow.card ≤ (insert 2 (odds.erase 9)).card :=
        Finset.card_le_card hsubset
      _ ≤ (odds.erase 9).card + 1 := Finset.card_insert_le 2 (odds.erase 9)
      _ = odds.card - 1 + 1 := by rw [Finset.card_erase_of_mem h9_mem]
      _ ≤ (Finset.Icc 1 a).card - 1 + 1 := by
        exact Nat.add_le_add_right (Nat.sub_le_sub_right Finset.card_image_le 1) 1
      _ = a := by
        rw [Nat.card_Icc]
        omega
      _ = (2 * a + 1) / 2 := by omega

