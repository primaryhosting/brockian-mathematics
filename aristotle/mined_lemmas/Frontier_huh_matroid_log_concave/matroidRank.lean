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

noncomputable def matroidRank (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, defined by the
Whitney rank-generating formula
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
