import Mathlib
namespace Brockian.Zsygmondy

open Polynomial

/-! ## Auxiliary results

The proof follows the classical cyclotomic-polynomial argument (Bang's theorem).
Write `Φ n a = eval (a : ℤ) (cyclotomic n ℤ)`.

* Any prime `q ∣ Φ n a` with `q ∤ n` is a primitive prime divisor of `aⁿ - 1`.
* If a prime `p ∣ Φ n a` divides `n`, writing `n = p ^ k * m` with `p ∤ m`, then the
  multiplicative order of `a` mod `p` is exactly `m`, hence `m ∣ p - 1`; in particular `p` is
  the largest prime factor of `n`, and `p ^ 2 ∤ Φ n a`.
* Consequently, if `Φ n a` has no prime factor coprime to `n`, then `Φ n a = p`.
* Finally `Φ n a > p`, a contradiction (except for `(a, n) = (2, 6)`).
-/

/-- The value of the `n`-th cyclotomic polynomial at a natural number `a`, as an integer. -/

lemma not_dvd_of_orderOf_eq {n a p : ℕ} (ha : 1 ≤ a)
    (hord : orderOf (a : ZMod p) = n) : ∀ m, 0 < m → m < n → ¬ p ∣ a ^ m - 1 := by
  intro m hm₁ hm₂ h
  have : (a : ZMod p) ^ m = 1 := by
    have h' : (p : ℤ) ∣ (a : ℤ) ^ m - 1 := by
      rw [← Int.natCast_pow]
      rw [← Int.natCast_one, ← Int.natCast_sub (Nat.one_le_pow m a ha)]
      exact Int.natCast_dvd_natCast.mpr h
    have h'' : (a : ZMod p) ^ m - 1 = 0 := by
      rw [sub_eq_zero]
      have h1 : ((a : ℤ) ^ m - (1 : ℤ) : ZMod p) = 0 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) ^ m - 1) p).mpr h'
        convert this using 2
        norm_cast
      simp only [Int.cast_natCast, Int.cast_one] at h1
      exact eq_of_sub_eq_zero h1
    simp [sub_eq_zero] at h''
    exact h''
  have hdiv : orderOf (a : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one this
  rw [hord] at hdiv
  exact Nat.not_dvd_of_pos_of_lt hm₁ hm₂ hdiv

/-! ### Primes dividing `n` -/

