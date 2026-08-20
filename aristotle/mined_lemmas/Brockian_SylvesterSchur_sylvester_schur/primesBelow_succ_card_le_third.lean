import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le_third {k : ℕ} (hk : 49 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 3 := by
  classical
  let ones : Finset ℕ := (Finset.Icc 0 (k / 6)).image fun t => 6 * t + 1
  let fives : Finset ℕ := (Finset.Icc 0 (k / 6)).image fun t => 6 * t + 5
  let base : Finset ℕ := insert 2 (insert 3 (ones ∪ fives))
  let trimmed : Finset ℕ := (((base.erase 1).erase 25).erase 35).erase 49
  have h1_base : 1 ∈ base := by
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨0, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h25_base : 25 ∈ base := by
    have h4 : 4 ≤ k / 6 := by omega
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨4, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h35_base : 35 ∈ base := by
    have h5 : 5 ≤ k / 6 := by omega
    dsimp [base, fives]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inr ?_
    rw [Finset.mem_image]
    refine ⟨5, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h49_base : 49 ∈ base := by
    have h8 : 8 ≤ k / 6 := by omega
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨8, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have hsubset : (k + 1).primesBelow ⊆ trimmed := by
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp_mem
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp_mem)
    have hp_base : p ∈ base := by
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      by_cases hp_three : p = 3
      · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr (Or.inl hp_three)
      have hmod_lt : p % 6 < 6 := Nat.mod_lt p (by norm_num)
      interval_cases hmod : p % 6
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hp_eq : 6 * (p / 6) + 1 = p := by
          have hdivmod := Nat.div_add_mod p 6
          omega
        have hp_div_mem : p / 6 ∈ Finset.Icc 0 (k / 6) := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
        have hp_ones : p ∈ ones := by
          rw [Finset.mem_image]
          exact ⟨p / 6, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl hp_ones
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hmod3 : p % 3 = 0 := by omega
        have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod3
        have hp_eq_three : p = 3 :=
          (hp_prime.dvd_iff_eq (by norm_num : 3 ≠ 1)).mp h3dvd
        exact (hp_three hp_eq_three).elim
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hp_eq : 6 * (p / 6) + 5 = p := by
          have hdivmod := Nat.div_add_mod p 6
          omega
        have hp_div_mem : p / 6 ∈ Finset.Icc 0 (k / 6) := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
        have hp_fives : p ∈ fives := by
          rw [Finset.mem_image]
          exact ⟨p / 6, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr hp_fives
    have hp_ne1 : p ≠ 1 := ne_of_gt hp_prime.one_lt
    have hp_ne25 : p ≠ 25 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    have hp_ne35 : p ≠ 35 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    have hp_ne49 : p ≠ 49 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    simpa [trimmed, hp_ne1, hp_ne25, hp_ne35, hp_ne49] using hp_base
  have hbase_card : base.card ≤ 2 * (k / 6 + 1) + 2 := by
    have hbase_le : base.card ≤ (ones ∪ fives).card + 2 := by
      dsimp [base]
      calc
        (insert 2 (insert 3 (ones ∪ fives))).card
            ≤ (insert 3 (ones ∪ fives)).card + 1 :=
          Finset.card_insert_le 2 _
        _ ≤ ((ones ∪ fives).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le 3 _) 1
        _ = (ones ∪ fives).card + 2 := by omega
    have hunion_le : (ones ∪ fives).card ≤ ones.card + fives.card :=
      Finset.card_union_le ones fives
    have hones_card : ones.card ≤ k / 6 + 1 := by
      calc
        ones.card ≤ (Finset.Icc 0 (k / 6)).card := Finset.card_image_le
        _ = k / 6 + 1 := by
          rw [Nat.card_Icc]
          omega
    have hfives_card : fives.card ≤ k / 6 + 1 := by
      calc
        fives.card ≤ (Finset.Icc 0 (k / 6)).card := Finset.card_image_le
        _ = k / 6 + 1 := by
          rw [Nat.card_Icc]
          omega
    omega
  have htrim_card : trimmed.card = base.card - 4 := by
    have h25_after1 : 25 ∈ base.erase 1 := by
      rw [Finset.mem_erase]
      exact ⟨by norm_num, h25_base⟩
    have h35_after25 : 35 ∈ (base.erase 1).erase 25 := by
      simp [h35_base]
    have h49_after35 : 49 ∈ ((base.erase 1).erase 25).erase 35 := by
      simp [h49_base]
    dsimp [trimmed]
    rw [Finset.card_erase_of_mem h49_after35]
    rw [Finset.card_erase_of_mem h35_after25]
    rw [Finset.card_erase_of_mem h25_after1]
    rw [Finset.card_erase_of_mem h1_base]
    omega
  calc
    (k + 1).primesBelow.card ≤ trimmed.card := Finset.card_le_card hsubset
    _ = base.card - 4 := htrim_card
    _ ≤ (2 * (k / 6 + 1) + 2) - 4 := Nat.sub_le_sub_right hbase_card 4
    _ ≤ k / 3 := by omega

