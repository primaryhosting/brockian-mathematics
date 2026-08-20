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

lemma prime_le_of_dvd_Phi {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : ∀ q, q.Prime → q ∣ n → q ≤ p := by
  intro q hq hqn
  by_cases hq_eq_p : q = p
  · exact hq_eq_p ▸ le_refl p
  · have hq_ne_p : q ≠ p := hq_eq_p
    have hq_coprime_p : Nat.Coprime q (p ^ (n.factorization p)) := by
      apply Nat.Coprime.pow_right
      exact hq.coprime_iff_not_dvd.mpr fun h => hq_ne_p (Nat.prime_dvd_prime_iff_eq hq hp |>.mp h)
    have hq_dvd_ordCompl : q ∣ n / p ^ (n.factorization p) := by
      have hpow_dvd_n : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
      have hmul : n = p ^ (n.factorization p) * (n / p ^ (n.factorization p)) := (Nat.mul_div_cancel' hpow_dvd_n).symm
      rw [hmul] at hqn
      exact hq_coprime_p.dvd_of_dvd_mul_left hqn
    have hordCompl_dvd_pred := ordCompl_dvd_pred hn hp hpn hdvd
    have hq_dvd_pred : q ∣ p - 1 := Nat.dvd_trans hq_dvd_ordCompl hordCompl_dvd_pred
    have hq_le_pred : q ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hq_dvd_pred
    exact Nat.le_trans hq_le_pred (Nat.sub_le p 1)

/-- If `p ∣ n` and `p ∣ Φ n a`, then `p` divides `a ^ (n / p) - 1`. -/
