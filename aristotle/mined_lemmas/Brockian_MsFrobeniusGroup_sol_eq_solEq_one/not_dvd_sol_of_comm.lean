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

lemma not_dvd_sol_of_comm {A : Type*} [Group A] [Finite A] (hcomm : ∀ x y : A, Commute x y)
    {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ p ∣ sol A m := by
  by_contra h
  -- The `m`-torsion is a subgroup, and Cauchy's theorem would give an element of order `p` in it.
  let powHom : A →* A :=
    { toFun := fun g => g ^ m, map_one' := by simp,
      map_mul' := fun a b => (hcomm a b).mul_pow m }
  let S := powHom.ker
  have hpS : p ∣ Nat.card S := h
  haveI : Fintype S := Fintype.ofFinite S
  have hpS' : p ∣ Fintype.card S := by rwa [Nat.card_eq_fintype_card] at hpS
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card p hpS'
  have hx_pow_m : (x : A) ^ m = 1 := x.2
  exact hm (by
    have h1 : orderOf (x : A) ∣ m := orderOf_dvd_of_pow_eq_one hx_pow_m
    rwa [Subgroup.orderOf_coe x, hx_order] at h1)

/-- `gcd (p ^ a) N` is `p ^ min a (v_p N)`. -/
