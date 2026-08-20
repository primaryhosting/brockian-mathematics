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

theorem matroidRank_unifOn (E : Finset α) (r : ℕ) {S : Finset α} (hS : S ⊆ E) :
    matroidRank (unifOn E r) (S : Set α) = min S.card r := by
  rw [matroidRank, eRk_unifOn E r hS, ← enat_cast_min]
  simp

/-- The characteristic polynomial of the uniform matroid, grouped by the size of the subset. -/
