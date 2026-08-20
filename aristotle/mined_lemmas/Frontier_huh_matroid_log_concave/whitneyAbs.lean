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

noncomputable def whitneyAbs (M : Matroid α) (E : Finset α) (i : ℕ) : ℕ :=
  ((charPoly M E).coeff i).natAbs

/-- In the free matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
