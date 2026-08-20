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

lemma matroidRank_freeOn {E S : Finset α} (h : S ⊆ E) :
    matroidRank (Matroid.freeOn (E : Set α)) (S : Set α) = S.card := by
  rw [matroidRank, Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on `E` is `(t - 1)^{|E|}`. -/
