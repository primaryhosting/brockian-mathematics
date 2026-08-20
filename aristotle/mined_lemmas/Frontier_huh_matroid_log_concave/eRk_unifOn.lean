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

theorem eRk_unifOn (E : Finset α) (r : ℕ) {S : Finset α} (hS : S ⊆ E) :
    (unifOn E r).eRk (S : Set α) = min (S.card : ℕ∞) (r : ℕ∞) := by
  apply le_antisymm
  · rw [Matroid.eRk_le_iff]
    intro I hIS hI
    rw [unifOn_indep_iff] at hI
    have hIfin : I.Finite := (S.finite_toSet).subset hIS
    refine le_min ?_ ?_
    · rw [← Set.encard_coe_eq_coe_finsetCard]
      exact Set.encard_le_encard hIS
    · rw [← hIfin.cast_ncard_eq]
      exact_mod_cast hI.2
  · rw [Matroid.le_eRk_iff]
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (n := min S.card r) (s := S) (by omega)
    refine ⟨(T : Set α), by exact_mod_cast hTS, ?_, ?_⟩
    · rw [unifOn_indep_iff]
      refine ⟨by exact_mod_cast hTS.trans hS, ?_⟩
      rw [Set.ncard_coe_finset, hT]
      omega
    · rw [Set.encard_coe_eq_coe_finsetCard, hT, enat_cast_min]

