import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma card_filter_card_le (n D : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).card
      = ∑ i ∈ range (D + 1), n.choose i := by
  classical
  have hEq : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D))
      = (range (D + 1)).biUnion (fun i => Finset.powersetCard i Finset.univ) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro h; exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [hEq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_powersetCard]
    simp
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_powersetCard]
    rintro S ⟨-, rfl⟩ ⟨-, h⟩
    exact hij h

end CS

import Mathlib

/-!
# Auxiliary lemmas

* an elementary growth estimate: `K * t ^ e ≤ 2 ^ t` for suitable arbitrarily large `t`;
* the existence of a finite field of characteristic `q` containing a nontrivial `p`-th root
  of unity, for distinct primes `p` and `q`.
-/

namespace CS

