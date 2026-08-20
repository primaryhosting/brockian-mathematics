import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma pPart_dvd_index_mul [Finite G] {H : Subgroup G} {p c : ℕ}
    (hc : p ^ ((Nat.card H).factorization p) ∣ c) :
    p ^ ((Nat.card G).factorization p) ∣ H.index * c := by
  have card_eq : Nat.card G = H.index * Nat.card H := by
    rw [Subgroup.index_mul_card]
  rw [card_eq]
  have h1 : (H.index * Nat.card H).factorization p =
      (H.index).factorization p + (Nat.card H).factorization p := by
    rw [Nat.factorization_mul]
    · simp
    · rw [Subgroup.index_eq_card]
      exact Nat.ne_of_gt (Nat.card_pos)
    · exact Nat.ne_of_gt (Nat.card_pos)
  rw [h1]
  rw [pow_add]
  refine Nat.mul_dvd_mul ?_ hc
  exact Nat.ordProj_dvd H.index p

/-- The central solutions of `x ^ m = 1` are the solutions inside the center. -/
