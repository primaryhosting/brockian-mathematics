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

lemma charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1) ^ E.card := by
  have h1 : charPoly (Matroid.freeOn (E : Set α)) E
      = ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [matroidRank_freeOn hS, matroidRank_freeOn (subset_refl E)]
  rw [h1, Finset.sum_powerset]
  have h2 : ∀ j ∈ Finset.range (E.card + 1),
      (∑ S ∈ Finset.powersetCard j E, (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card))
        = (-1 : Polynomial ℤ) ^ j * X ^ (E.card - j) * (E.card.choose j : Polynomial ℤ) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]), Finset.sum_const,
      Finset.card_powersetCard]
    simp [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl h2]
  have h3 : ((-1 : Polynomial ℤ) + X) ^ E.card
      = ∑ j ∈ Finset.range (E.card + 1),
        (-1 : Polynomial ℤ) ^ j * X ^ (E.card - j) * (E.card.choose j : Polynomial ℤ) := by
    rw [add_pow]
  rw [← h3]
  ring

/-- The Whitney numbers of the free matroid are binomial coefficients. -/
