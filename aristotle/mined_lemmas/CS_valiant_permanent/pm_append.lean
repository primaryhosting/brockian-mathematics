import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem pm_append (M : ι → ι → R) :
    ∀ (l₁ l₂ : List ι) (C : Finset ι),
      pm M (l₁ ++ l₂) C = ∑ D ∈ C.powersetCard l₁.length, pm M l₁ D * pm M l₂ (C \ D) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ C
      simp
  | cons r rs ih =>
      intro l₂ C
      rw [List.cons_append, pm_cons]
      have h1 : ∀ c ∈ C, M r c * pm M (rs ++ l₂) (C.erase c)
          = ∑ D ∈ (C.erase c).powersetCard rs.length,
              M r c * pm M rs D * pm M l₂ (C \ insert c D) := by
        intro c hc
        rw [ih, Finset.mul_sum]
        refine Finset.sum_congr rfl fun D hD => ?_
        have hCD : C \ insert c D = (C.erase c) \ D := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
          tauto
        rw [hCD, mul_assoc]
      rw [Finset.sum_congr rfl h1]
      have h2 : ∀ D' ∈ C.powersetCard (rs.length + 1),
          pm M (r :: rs) D' * pm M l₂ (C \ D')
            = ∑ c ∈ D', M r c * pm M rs (D'.erase c) * pm M l₂ (C \ D') := by
        intro D' _
        rw [pm_cons, Finset.sum_mul]
      rw [List.length_cons, Finset.sum_congr rfl h2, Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (i := fun p => (⟨insert p.1 p.2, p.1⟩ : (_ : Finset ι) × ι))
        (j := fun q => (⟨q.2, q.1.erase q.2⟩ : (_ : ι) × Finset ι)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp ⊢
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hc
          · exact (Finset.mem_erase.mp (hDsub hx)).2
        · rw [Finset.card_insert_of_notMem hcD, hDcard]
      · rintro ⟨D', c⟩ hq
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
        obtain ⟨⟨hDsub, hDcard⟩, hc⟩ := hq
        refine ⟨hDsub hc, ?_, ?_⟩
        · intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hDsub (Finset.mem_erase.mp hx).2⟩
        · rw [Finset.card_erase_of_mem hc, hDcard]
          omega
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        simp [Finset.erase_insert hcD]
      · rintro ⟨D', c⟩ hq
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
        simp [Finset.insert_erase hq.2]
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        simp [Finset.erase_insert hcD]

/-- If some available column cannot be covered by any of the rows, there is nothing to count. -/
