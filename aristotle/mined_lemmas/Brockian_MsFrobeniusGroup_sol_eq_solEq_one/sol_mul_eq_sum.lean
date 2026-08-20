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

lemma sol_mul_eq_sum [Fintype G] {p α u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    sol G (p ^ α * u) =
      ∑ w ∈ univ.filter (fun w : G => w ^ u = 1),
        sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ α) := by
  obtain ⟨e, f, he, hf, he1, hf1, hef⟩ :=
    exists_crt_exponents hp hu (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p)))
  rw [sol_mul_eq_sum_aux he hf he1 hf1 hef]
  exact Finset.sum_congr rfl fun w _ => card_commuting_sol_eq w (p ^ α)

/-- The size of a conjugacy class is the index of the centralizer. -/
