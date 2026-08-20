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

lemma prime_pow_dvd_sol [Fintype G] {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (min (n.factorization p) ((Nat.card G).factorization p)) ∣ sol G n := by
  set α := n.factorization p with hα
  set u := n / p ^ α with hu_def
  have hn_eq : n = p ^ α * u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hu : ¬ p ∣ u := Nat.not_dvd_ordCompl hp hn
  rw [hn_eq, sol_mul_eq_sum hp hu]
  refine dvd_sum_of_conj_invariant (d := p ^ (min α ((Nat.card G).factorization p)))
    (fun w => sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ α))
    (fun g w => sol_centralizer_conj g w (p ^ α))
    (univ.filter (fun w : G => w ^ u = 1)) ?_ ?_
  · intro g w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [conj_pow, hw]
    group
  · intro w _
    refine pPart_min_dvd_index_mul ?_
    exact sol_prime_pow_dvd (G := ↥(Subgroup.centralizer ({w} : Set G))) hp

/-- Frobenius's theorem: `gcd n |G|` divides the number of solutions of `x ^ n = 1`. -/
