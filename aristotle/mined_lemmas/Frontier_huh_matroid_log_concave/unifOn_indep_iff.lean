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

theorem unifOn_indep_iff (E : Finset α) (r : ℕ) (I : Set α) :
    (unifOn E r).Indep I ↔ I ⊆ (E : Set α) ∧ I.ncard ≤ r := by
  simp [unifOn]

