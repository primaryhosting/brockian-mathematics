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

lemma sol_mul_eq_sum_aux [Fintype G] {p α u e f : ℕ}
    (he : p ^ α ∣ e) (hf : u ∣ f) (he1 : e ≡ 1 [MOD u]) (hf1 : f ≡ 1 [MOD p ^ α])
    (hef : (e + f) ≡ 1 [MOD p ^ α * u]) :
    sol G (p ^ α * u) = ∑ w ∈ univ.filter (fun w : G => w ^ u = 1),
        (univ.filter (fun v : G => v ^ (p ^ α) = 1 ∧ Commute w v)).card := by
  rw [sol_eq_card_filter]
  have hmaps : ∀ x ∈ univ.filter (fun x : G => x ^ (p ^ α * u) = 1),
      x ^ e ∈ univ.filter (fun w : G => w ^ u = 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← pow_mul]
    exact pow_eq_one_of_dvd_of_pow_eq_one hx (mul_dvd_mul_right he u)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact sol_mul_eq_sum_fiber he hf he1 hf1 hef w hw

/-- Counting solutions in the centralizer of `w`. -/
