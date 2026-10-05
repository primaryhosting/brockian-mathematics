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

theorem pm_block (M : ι → ι → R) (l₁ l₂ : List ι) (C₁ C₂ : Finset ι)
    (hsupp₁ : ∀ r ∈ l₁, ∀ c, c ∉ C₁ → M r c = 0)
    (hdisj : Disjoint C₁ C₂) (hcard : C₁.card = l₁.length) :
    pm M (l₁ ++ l₂) (C₁ ∪ C₂) = pm M l₁ C₁ * pm M l₂ C₂ := by
  rw [pm_append, Finset.sum_eq_single C₁]
  · congr 1
    rw [Finset.union_sdiff_cancel_left hdisj]
  · intro D hD hne
    rw [Finset.mem_powersetCard] at hD
    by_cases hsub : D ⊆ C₁
    · exact absurd (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hD.2])) hne
    · rw [pm_eq_zero_of_not_subset M C₁ _ _ hsupp₁ hsub, zero_mul]
  · intro h
    exact absurd (Finset.mem_powersetCard.mpr ⟨Finset.subset_union_left, hcard⟩) h

/-! ### `pm` computes the permanent -/

variable [Fintype ι]

/-- The bijections (as normalized functions) from the rows in `l` onto the columns in `C`. -/
