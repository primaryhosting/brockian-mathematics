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

lemma sol_mul_eq_sum_fiber [Fintype G] {p α u e f : ℕ}
    (he : p ^ α ∣ e) (hf : u ∣ f) (he1 : e ≡ 1 [MOD u]) (hf1 : f ≡ 1 [MOD p ^ α])
    (hef : (e + f) ≡ 1 [MOD p ^ α * u]) (w : G) (hw : w ^ u = 1) :
    ((univ.filter (fun x : G => x ^ (p ^ α * u) = 1)).filter (fun x : G => x ^ e = w)).card
      = (univ.filter (fun v : G => v ^ (p ^ α) = 1 ∧ Commute w v)).card := by
  refine Finset.card_bij' (fun x _ => x ^ f) (fun v _ => w * v) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨sol_aux_pow_f_eq_one hf hx.1, ?_⟩
    rw [← hx.2]
    exact (Commute.refl x).pow_pow e f
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨sol_aux_mul_pow_eq_one hw hv.1 hv.2, sol_aux_mul_pow_e he he1 hw hv.1 hv.2⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h := sol_aux_pow_e_mul_pow_f hef hx.1
    rw [hx.2] at h
    exact h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact sol_aux_mul_pow_f hf hf1 hw hv.1 hv.2

/-- The bijection `x ↦ (x ^ e, x ^ f)` between solutions of `x ^ (p ^ α * u) = 1` and pairs
consisting of a solution `w` of `w ^ u = 1` and a solution `v` of `v ^ (p ^ α) = 1` commuting
with `w`. -/
