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

lemma card_commuting_sol_eq [Fintype G] (w : G) (n : ℕ) :
    (univ.filter (fun v : G => v ^ n = 1 ∧ Commute w v)).card
      = sol ↥(Subgroup.centralizer ({w} : Set G)) n := by
  have he : {v : G // v ^ n = 1 ∧ Commute w v}
      ≃ {x : ↥(Subgroup.centralizer ({w} : Set G)) // x ^ n = 1} :=
    { toFun := fun x =>
        ⟨⟨x.val, by
            rw [Subgroup.mem_centralizer_iff]
            rintro y rfl
            exact x.property.2⟩,
          Subtype.ext (by simpa using x.property.1)⟩
      invFun := fun x =>
        ⟨x.val.val, ⟨by
            have h := congrArg Subtype.val x.prop
            simpa using h,
          (Subgroup.mem_centralizer_iff.mp x.val.property) w rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [sol, ← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Primary decomposition identity.**  Writing `n = p ^ α * u` with `p ∤ u`, every element of `G`
factors uniquely as a commuting product of a `p`-element and a `p'`-element; this gives a bijection
between the solutions of `x ^ n = 1` and the pairs `(w, v)` where `w ^ u = 1` and `v` lies in the
centralizer of `w` with `v ^ (p ^ α) = 1`. -/
