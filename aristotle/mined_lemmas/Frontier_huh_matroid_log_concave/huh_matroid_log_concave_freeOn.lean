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

theorem huh_matroid_log_concave_freeOn (E : Finset α) (i : ℕ) :
    whitneyAbs (Matroid.freeOn (E : Set α)) E i * whitneyAbs (Matroid.freeOn (E : Set α)) E (i + 2)
      ≤ whitneyAbs (Matroid.freeOn (E : Set α)) E (i + 1) ^ 2 := by
  simp only [whitneyAbs_freeOn, pow_two]
  exact choose_log_concave E.card i

end Frontier

