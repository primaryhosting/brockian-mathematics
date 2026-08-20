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

private lemma natAbs_signed (m c : ℕ) : ((-1 : ℤ) ^ m * (c : ℤ)).natAbs = c := by
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, one_mul, Int.natAbs_natCast]
  · rw [h.neg_one_pow, neg_one_mul, Int.natAbs_neg, Int.natAbs_natCast]

/-- The coefficients of the characteristic polynomial of `U_{r,E}`, as a sum over subset sizes. -/
