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

noncomputable def unifOn (E : Finset α) (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite (E := (E : Set α)) E.finite_toSet
    (fun I => I ⊆ (E : Set α) ∧ I.ncard ≤ r)
    ⟨by simp, by simp⟩
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, le_trans (Set.ncard_le_ncard hIJ
      (E.finite_toSet.subset hJ.1)) hJ.2⟩)
    (by
      rintro I J ⟨hIE, hIr⟩ ⟨hJE, hJr⟩ hlt
      have hIfin : I.Finite := E.finite_toSet.subset hIE
      obtain ⟨e, heJ, heI⟩ : ∃ e ∈ J, e ∉ I := by
        by_contra h
        push_neg at h
        exact absurd (Set.ncard_le_ncard h hIfin) (by omega)
      refine ⟨e, heJ, heI, Set.insert_subset (hJE heJ) hIE, ?_⟩
      rw [Set.ncard_insert_of_notMem heI hIfin]
      omega)
    (fun _ h => h.1)).matroid

