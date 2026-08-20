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

theorem gcd_dvd_sol [Fintype G] (n : ℕ) : Nat.gcd n (Nat.card G) ∣ sol G n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : sol G 0 = Nat.card G := by
      simp [sol]
    simp [this]
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hg : Nat.gcd n (Nat.card G) ≠ 0 := Nat.gcd_ne_zero_left hn
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  have hk : k ≤ (Nat.gcd n (Nat.card G)).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hg).mp hpk
  have hfg : (Nat.gcd n (Nat.card G)).factorization p
      = min (n.factorization p) ((Nat.card G).factorization p) := by
    rw [Nat.factorization_gcd hn hG]
    simp [Nat.min_def]
  rw [hfg] at hk
  exact dvd_trans (pow_dvd_pow p hk) (prime_pow_dvd_sol hp hn)

/-- Frobenius's theorem: for a finite group G and any n, gcd(n, |G|) divides the number of
    solutions of xⁿ = 1 in G. -/
