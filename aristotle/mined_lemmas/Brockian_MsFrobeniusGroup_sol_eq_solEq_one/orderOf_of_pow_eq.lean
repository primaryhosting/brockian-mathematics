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

lemma orderOf_of_pow_eq [Finite G] {p a k : ℕ} (hp : p.Prime) (hk : 0 < k) {x y : G}
    (hy : orderOf y = p ^ k) (hxy : x ^ (p ^ a) = y) : orderOf x = p ^ (a + k) := by
  -- First show x ^ (p ^ (a + k)) = 1
  have hx_pow : x ^ (p ^ (a + k)) = 1 := by
    calc x ^ (p ^ (a + k)) = x ^ (p ^ a * p ^ k) := by rw [pow_add]
      _ = (x ^ (p ^ a)) ^ (p ^ k) := by rw [← pow_mul]
      _ = y ^ (p ^ k) := by rw [hxy]
      _ = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  -- So orderOf x divides p ^ (a + k)
  have hdiv : orderOf x ∣ p ^ (a + k) := orderOf_dvd_of_pow_eq_one hx_pow
  -- orderOf x is a power of p
  rw [Nat.dvd_prime_pow hp] at hdiv
  obtain ⟨m, hm_le, hm_eq⟩ := hdiv
  -- Use that orderOf (x ^ (p ^ a)) = orderOf x / gcd(orderOf x, p ^ a)
  have hy' : orderOf (x ^ (p ^ a)) = p ^ k := by rw [hxy, hy]
  -- Use orderOf_pow to relate orderOf (x ^ n) to orderOf x
  have hpow := orderOf_pow (x := x) (n := p ^ a)
  rw [hm_eq] at hpow
  rw [hpow] at hy'
  -- gcd(p^m, p^a) = p^(min m a)
  rw [Nat.gcd_comm] at hy'
  have hgcd : Nat.gcd (p ^ a) (p ^ m) = p ^ min a m := by
    rcases le_total a m with ham | ham
    · rw [min_eq_left ham]
      simp [Nat.gcd_eq_left (pow_dvd_pow p ham)]
    · rw [min_eq_right ham]
      simp [Nat.gcd_eq_right (pow_dvd_pow p ham)]
  rw [hgcd] at hy'
  -- So p^(m - min a m) = p^k, hence m - min a m = k
  have hminm : min a m ≤ m := min_le_right a m
  have hdiv_eq : p ^ k * p ^ min a m = p ^ m := by
    have h1 : p ^ min a m ∣ p ^ m := pow_dvd_pow p hminm
    rw [← Nat.mul_div_cancel' h1]
    simp [hy', Nat.mul_comm]
  rw [← pow_add] at hdiv_eq
  have hexp : k + min a m = m := Nat.pow_right_injective hp.one_lt hdiv_eq
  have hexp' : m - min a m = k := by omega
  -- Since k > 0, we have m > min a m, so m > a
  by_cases hm : m ≤ a
  · -- If m ≤ a, then min a m = m, so m - m = k = 0, contradicting k > 0
    rw [min_eq_right hm] at hexp
    simp at hexp
    linarith
  · -- If m > a, then min a m = a, so m - a = k, hence m = a + k
    push Not at hm
    rw [min_eq_left (le_of_lt hm)] at hexp
    rw [hm_eq]
    rw [← hexp]
    rw [add_comm]

/-- The solutions of `x ^ (p ^ a) = y` generating a fixed cyclic subgroup: there are exactly
`p ^ a` of them. -/
