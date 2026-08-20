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

lemma Phi_pow_reduction {p m : ℕ} (hp : p.Prime) (k : ℕ) (x : ℤ) :
    (cyclotomic (p ^ (k + 1) * m) ℤ).eval x = (cyclotomic (m * p) ℤ).eval (x ^ (p ^ k)) := by
  induction k generalizing x with
  | zero => simp [mul_comm]
  | succ k ih =>
    have hdvd : p ∣ p ^ (k + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero k)) m
    have h2 := congrArg (Polynomial.eval x) (cyclotomic_expand_eq_cyclotomic hp hdvd ℤ)
    rw [expand_eval] at h2
    have hxx : p ^ (k + 1) * m * p = p ^ (k + 1 + 1) * m := by ring
    rw [hxx] at h2
    rw [← h2, ih (x ^ p), ← pow_mul, ← pow_succ']

/-- Lower bound for `Φ_{m p}` in terms of `((y ^ p - 1) / (y + 1)) ^ φ m`, over the reals. -/
