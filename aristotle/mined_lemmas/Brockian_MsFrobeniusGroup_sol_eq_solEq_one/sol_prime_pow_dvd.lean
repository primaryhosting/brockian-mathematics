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

theorem sol_prime_pow_dvd [Fintype G] {p a : ℕ} (hp : p.Prime) :
    p ^ (min a ((Nat.card G).factorization p)) ∣ sol G (p ^ a) := by
  have hcard_pos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [sol_eq_gcd (p ^ a), gcd_prime_pow hp a (Nat.card G) hcard_pos]
  by_cases hab : a ≤ (Nat.card G).factorization p
  · have h1 : p ^ (Nat.card G).factorization p ∣ sol G (p ^ (Nat.card G).factorization p) :=
      pPart_dvd_sol_pPart hp (Nat.card G) G rfl
    have h2 : sol G (p ^ (Nat.card G).factorization p) ≡ sol G (p ^ a) [MOD p ^ a] :=
      sol_modEq_le hp hab
    rw [min_eq_left hab]
    exact (Nat.modEq_zero_iff_dvd.1
      (((Nat.modEq_zero_iff_dvd.2 ((pow_dvd_pow p hab).trans h1)).symm.trans h2).symm))
  · rw [min_eq_right (Nat.le_of_not_le hab)]
    exact pPart_dvd_sol_pPart hp (Nat.card G) G rfl

/-- A version of `pPart_dvd_index_mul` with a truncated exponent. -/
