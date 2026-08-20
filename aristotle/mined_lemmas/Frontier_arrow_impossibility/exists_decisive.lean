import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem exists_decisive (hV : FinitelyMany V) (huna : Unanimous F) (hiia : IIA F)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ i : V, Decisive F i a c := by
  obtain ⟨l, hl⟩ := hV
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have L1 := tri_lt_iff a b c hab hac hbc
  have L2 := tri_lt_iff a c b hac hab hcb
  have L3 := tri_lt_iff b a c hba hbc hac
  have L4 := tri_lt_iff b c a hbc hba hca
  have L5 := tri_lt_iff c a b hca hcb hab
  -- in every `bTop` profile, `b` is extremal for each voter
  have hext : ∀ S : List V, ∀ j : V,
      (((bTop a b c S) j).lt b a ∧ ((bTop a b c S) j).lt b c) ∨
      (((bTop a b c S) j).lt a b ∧ ((bTop a b c S) j).lt c b) := by
    intro S j
    by_cases hj : j ∈ S
    · rw [bTop_mem hj]
      simp only [L3]
      simp [hab, hac, hbc, hba, hca, hcb]
    · rw [bTop_not_mem hj]
      simp only [L2]
      simp [hab, hac, hbc, hba, hca, hcb]
  let T : List V → Prop := fun S =>
    (F (bTop a b c S)).lt b a ∧ (F (bTop a b c S)).lt b c
  have hTinv : ∀ u w : List V, (∀ x, x ∈ u ↔ x ∈ w) → (T u ↔ T w) := by
    intro u w huw
    have heq : bTop a b c u = bTop a b c w := by
      funext j
      by_cases hj : j ∈ u
      · rw [bTop_mem hj, bTop_mem ((huw j).mp hj)]
      · rw [bTop_not_mem hj, bTop_not_mem (fun hc => hj ((huw j).mpr hc))]
    exact ⟨fun h => ⟨heq ▸ h.1, heq ▸ h.2⟩, fun h => ⟨heq ▸ h.1, heq ▸ h.2⟩⟩
  have hT0 : ¬ T ([] : List V) := by
    have h1 : (F (bTop a b c ([] : List V))).lt a b := by
      refine huna _ a b ?_
      intro j
      rw [bTop_not_mem (S := ([] : List V)) (List.not_mem_nil)]
      simp only [L2]
      simp [hac, hba]
    intro hc
    exact (F (bTop a b c ([] : List V))).asym h1 hc.1
  have hT1 : T l := by
    constructor <;>
    · refine huna _ _ _ ?_
      intro j
      rw [bTop_mem (hl j)]
      simp only [L3]
      simp [hab, hac, hba, hcb]
  obtain ⟨S, i, hiS, hnS, hins⟩ := exists_pivot T hTinv hT0 l hT1
  have hbot : (F (bTop a b c S)).lt a b ∧ (F (bTop a b c S)).lt c b := by
    rcases extremal huna hiia hab hac hbc (bTop a b c S) (hext S) with h | h
    · exact absurd h hnS
    · exact h
  refine ⟨i, ?_⟩
  intro Q hQ
  -- `R` agrees with `bTop S` on the pair `(a, b)`
  have hRab : (F (pivProfile a b c S i Q)).lt a b := by
    refine (iia_pair hiia _ (bTop a b c S) a b hab ?_).mpr hbot.1
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_self, bTop_not_mem hiS]
      simp only [L1, L2]
      simp [hab, hac, hbc, hba]
    · by_cases hjS : j ∈ S
      · rw [bTop_mem hjS]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_mem_pos hj hjS hq]
        · rw [pivProfile_mem_neg hj hjS hq]
          simp only [L3, L4]
          simp [hab, hac, hbc, hba]
      · rw [bTop_not_mem hjS]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_not_mem_pos hj hjS hq]
        · rw [pivProfile_not_mem_neg hj hjS hq]
          simp only [L2, L5]
          simp [hac, hbc, hba]
  -- `R` agrees with `bTop (i :: S)` on the pair `(b, c)`
  have hRbc : (F (pivProfile a b c S i Q)).lt b c := by
    refine (iia_pair hiia _ (bTop a b c (i :: S)) b c hbc ?_).mpr hins.2
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_self, bTop_mem (S := j :: S) (by simp)]
      simp only [L1, L3]
      simp [hba, hca, hcb]
    · by_cases hjS : j ∈ S
      · rw [bTop_mem (S := i :: S) (by simp [hjS])]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_mem_pos hj hjS hq]
        · rw [pivProfile_mem_neg hj hjS hq]
          simp only [L3, L4]
          simp [hbc, hba, hca, hcb]
      · rw [bTop_not_mem (S := i :: S) (by simp [hj, hjS])]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_not_mem_pos hj hjS hq]
        · rw [pivProfile_not_mem_neg hj hjS hq]
          simp only [L2, L5]
          simp [hbc, hba, hca, hcb]
  have hRac : (F (pivProfile a b c S i Q)).lt a c :=
    (F (pivProfile a b c S i Q)).tr hRab hRbc
  -- `R` agrees with `Q` on the pair `(a, c)`
  refine (iia_pair hiia _ Q a c hac ?_).mp hRac
  intro j
  by_cases hj : j = i
  · subst hj
    rw [pivProfile_self]
    simp only [L1]
    simp [hab, hca, hQ]
  · by_cases hjS : j ∈ S
    · by_cases hq : (Q j).lt a c
      · rw [pivProfile_mem_pos hj hjS hq]
        simp only [L3]
        simp [hab, hcb, hq]
      · rw [pivProfile_mem_neg hj hjS hq]
        simp only [L4]
        simp [hab, hac, hca, hcb, hq]
    · by_cases hq : (Q j).lt a c
      · rw [pivProfile_not_mem_pos hj hjS hq]
        simp only [L2]
        simp [hac, hca, hcb, hq]
      · rw [pivProfile_not_mem_neg hj hjS hq]
        simp only [L5]
        simp [hac, hcb, hq]

/-- Two voters decisive for opposite ordered pairs must be the same voter. -/
