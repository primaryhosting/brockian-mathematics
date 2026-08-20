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

lemma sum_central_eq [Fintype G] (m n : ℕ) :
    ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
      sol ↥(Subgroup.centralizer ({w} : Set G)) n
      = sol ↥(Subgroup.center G) m * sol G n := by
  have h_sol_centralizer_eq : ∀ w : G, w ∈ Subgroup.center G →
      sol ↥(Subgroup.centralizer ({w} : Set G)) n = sol G n := by
    intro w hw
    have : Subgroup.centralizer ({w} : Set G) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_iff]
      exact hw.comm g
    rw [this]
    exact sol_top n
  calc ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
        sol ↥(Subgroup.centralizer ({w} : Set G)) n
      = ∑ _w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G), sol G n :=
        Finset.sum_congr rfl fun w hw => h_sol_centralizer_eq w ((Finset.mem_filter.mp hw).2).2
    _ = (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).card * sol G n := by
        simp [Finset.sum_const, smul_eq_mul]
    _ = sol ↥(Subgroup.center G) m * sol G n := by rw [card_center_sol]

/-- The contribution of the non-central elements to the primary decomposition identity is
divisible by the `p`-part of `|G|`. -/
