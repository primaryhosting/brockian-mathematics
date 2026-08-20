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

lemma sol_modEq_succ [Fintype G] {p a : ℕ} (hp : p.Prime) :
    sol G (p ^ (a + 1)) ≡ sol G (p ^ a) [MOD p ^ a] := by
  rw [pow_succ', mul_comm, sol_mul_eq_sum_solEq (p ^ a) p]
  set S := Finset.filter (fun y : G => y ^ p = 1) Finset.univ with hS
  set T := Finset.filter (fun y : G => y ^ p = 1 ∧ y ≠ 1) Finset.univ with hT
  have hS_eq : S = {1} ∪ T := by
    ext x
    simp only [hS, hT, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hx : x = 1 <;> simp [hx]
  have h1_disj : Disjoint ({1} : Finset G) T := by
    rw [Finset.disjoint_left]
    simp [hT]
  rw [hS_eq, Finset.sum_union h1_disj]
  simp [solEq, sol]
  apply Finset.dvd_sum
  intro y hy
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have hy_order : orderOf y = p := by
    have h := orderOf_dvd_of_pow_eq_one hy.1
    rw [Nat.dvd_prime hp] at h
    cases h with
    | inl h => exact absurd (orderOf_eq_one_iff.mp h) hy.2
    | inr h => exact h
  have hk : orderOf y = p ^ (1 : ℕ) := by rw [hy_order, pow_one]
  have := @solEq_prime_pow_dvd _ _ _ p a 1 hp y one_pos hk
  rwa [solEq, Nat.card_eq_fintype_card] at this

/-- `sol G (p ^ b) ≡ sol G (p ^ a)` modulo `p ^ a` for `a ≤ b`. -/
