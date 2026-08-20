import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le_fourth {k : ℕ} (hk : 2500 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 4 := by
  classical
  let residues : Finset ℕ := (Finset.range 210).filter (fun r => Nat.Coprime r 210)
  let candidates : Finset ℕ := (Finset.Icc 0 (k / 210)).biUnion fun q =>
    residues.image fun r => 210 * q + r
  let base : Finset ℕ := insert 2 (insert 3 (insert 5 (insert 7 candidates)))
  have hsubset : (k + 1).primesBelow ⊆ base := by
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp_mem
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp_mem)
    by_cases hp2 : p = 2
    · exact Finset.mem_insert.mpr (Or.inl hp2)
    by_cases hp3 : p = 3
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inl hp3
    by_cases hp5 : p = 5
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_insert.mpr <| Or.inl hp5
    by_cases hp7 : p = 7
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inl hp7
    have hcop : p.Coprime 210 := prime_coprime_210 hp_prime hp2 hp3 hp5 hp7
    have hres : p % 210 ∈ residues := by
      dsimp [residues]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.mod_lt p (by norm_num)), coprime_mod_210 hcop⟩
    have hq : p / 210 ∈ Finset.Icc 0 (k / 210) := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
    have hp_eq : 210 * (p / 210) + p % 210 = p := Nat.div_add_mod p 210
    have hmem_cand : p ∈ candidates := by
      dsimp [candidates]
      rw [Finset.mem_biUnion]
      refine ⟨p / 210, hq, ?_⟩
      rw [Finset.mem_image]
      exact ⟨p % 210, hres, hp_eq⟩
    exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr hmem_cand
  have hres_card : residues.card = 48 := by decide
  have hcand_card : candidates.card ≤ (k / 210 + 1) * 48 := by
    calc
      candidates.card ≤ (Finset.Icc 0 (k / 210)).card * 48 := by
        refine Finset.card_biUnion_le_card_mul _ _ 48 ?_
        intro q hq
        calc
          ((residues.image fun r => 210 * q + r).card) ≤ residues.card :=
            Finset.card_image_le
          _ = 48 := hres_card
      _ = (k / 210 + 1) * 48 := by
        rw [Nat.card_Icc]
        omega
  have hbase_card : base.card ≤ candidates.card + 4 := by
    dsimp [base]
    calc
      (insert 2 (insert 3 (insert 5 (insert 7 candidates)))).card
          ≤ (insert 3 (insert 5 (insert 7 candidates))).card + 1 :=
        Finset.card_insert_le 2 _
      _ ≤ ((insert 5 (insert 7 candidates)).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le 3 _) 1
      _ ≤ (((insert 7 candidates).card + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_insert_le 5 _) 1) 1
      _ ≤ (((candidates.card + 1) + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le 7 _) 1) 1) 1
      _ = candidates.card + 4 := by omega
  calc
    (k + 1).primesBelow.card ≤ base.card := Finset.card_le_card hsubset
    _ ≤ candidates.card + 4 := hbase_card
    _ ≤ (k / 210 + 1) * 48 + 4 := Nat.add_le_add_right hcand_card 4
    _ ≤ k / 4 := by omega

