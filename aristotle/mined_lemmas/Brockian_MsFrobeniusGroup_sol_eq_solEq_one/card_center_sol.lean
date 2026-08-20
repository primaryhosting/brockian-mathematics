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

lemma card_center_sol [Fintype G] (m : ℕ) :
    (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).card
      = sol ↥(Subgroup.center G) m := by
  unfold sol
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]
  have equiv : {w : G | w ^ m = 1 ∧ w ∈ Subgroup.center G} ≃ {x : Subgroup.center G | x ^ m = 1} :=
    {
      toFun := fun ⟨w, hw⟩ => ⟨⟨w, hw.2⟩, Subtype.ext hw.1⟩
      invFun := fun ⟨x, hx⟩ => ⟨x.1, ⟨by rw [← Subgroup.coe_pow]; rw [hx]; simp, x.2⟩⟩
      left_inv := fun ⟨w, hw⟩ => by simp
      right_inv := fun ⟨x, hx⟩ => by simp
    }
  convert Fintype.card_congr equiv using 2 <;> simp [Fintype.card_subtype]

/-- Every element satisfies `x ^ |G| = 1`. -/
