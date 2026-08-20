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

private lemma enat_cast_min (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) (b : ℕ∞) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h : (a : ℕ∞) ≤ b)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h : (b : ℕ∞) ≤ a)]

