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

lemma whitneyAbs_freeOn (E : Finset α) (i : ℕ) :
    whitneyAbs (Matroid.freeOn (E : Set α)) E i = E.card.choose i := by
  rw [whitneyAbs, charPoly_freeOn]
  have : ((X : Polynomial ℤ) - 1) ^ E.card = (X + C (-1 : ℤ)) ^ E.card := by
    simp [sub_eq_add_neg]
  rw [this, Polynomial.coeff_X_add_C_pow]
  rw [Int.natAbs_mul]
  have hpow : ((-1 : ℤ) ^ (E.card - i)).natAbs = 1 := by
    rcases Nat.even_or_odd (E.card - i) with h | h
    · rw [h.neg_one_pow]; rfl
    · rw [h.neg_one_pow]; rfl
  rw [hpow, one_mul, Int.natAbs_natCast]

/-- Binomial coefficients form a log-concave sequence. -/
