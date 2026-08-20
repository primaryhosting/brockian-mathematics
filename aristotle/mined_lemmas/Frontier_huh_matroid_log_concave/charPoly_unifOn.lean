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

theorem charPoly_unifOn (E : Finset α) (r : ℕ) (hr : r ≤ E.card) :
    charPoly (unifOn E r) E =
      ∑ k ∈ Finset.range (E.card + 1),
        C ((-1 : ℤ) ^ k * (E.card.choose k : ℤ)) * X ^ (r - min k r) := by
  have h1 : charPoly (unifOn E r) E
      = ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ (r - min S.card r) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [matroidRank_unifOn E r hS, matroidRank_unifOn E r (subset_refl E),
      min_eq_right hr]
  rw [h1, Finset.sum_powerset]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]),
    Finset.sum_const, Finset.card_powersetCard]
  simp [nsmul_eq_mul]
  ring

/-- The partial alternating sums of binomial coefficients. -/
