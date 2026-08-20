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

theorem coeff_charPoly_unifOn (E : Finset α) (r i : ℕ) (hr : r ≤ E.card) :
    (charPoly (unifOn E r) E).coeff i
      = ∑ k ∈ Finset.range (E.card + 1),
          ((-1 : ℤ) ^ k * (E.card.choose k : ℤ)) * (if i = r - min k r then 1 else 0) := by
  rw [charPoly_unifOn E r hr, Polynomial.finset_sum_coeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- The coefficients of the characteristic polynomial of `U_{r,E}` in positive degrees. -/
