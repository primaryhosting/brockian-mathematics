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

lemma real_lower_bound {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m) {y : ℝ}
    (hy : 2 ≤ y) : ((y ^ p - 1) / (y + 1)) ^ (Nat.totient m) < (cyclotomic (m * p) ℝ).eval y := by
  have hy1 : (1:ℝ) < y := by linarith
  have hyp : (1:ℝ) < y ^ p := one_lt_pow₀ hy1 hp.ne_zero
  have key : (cyclotomic m ℝ).eval (y ^ p)
      = (cyclotomic (m * p) ℝ).eval y * (cyclotomic m ℝ).eval y := by
    have h2 := congrArg (Polynomial.eval y) (cyclotomic_expand_eq_cyclotomic_mul hp hpm ℝ)
    rw [expand_eval] at h2
    simpa using h2
  have hlow : (y ^ p - 1) ^ (Nat.totient m) < (cyclotomic m ℝ).eval (y ^ p) :=
    sub_one_pow_totient_lt_cyclotomic_eval hm hyp
  have hup : (cyclotomic m ℝ).eval y ≤ (y + 1) ^ (Nat.totient m) :=
    cyclotomic_eval_le_add_one_pow_totient hy1 m
  have hpos : 0 < (cyclotomic m ℝ).eval y := cyclotomic_pos' m hy1
  have hy1' : (0:ℝ) < y + 1 := by linarith
  rw [div_pow, div_lt_iff₀ (by positivity)]
  calc (y ^ p - 1) ^ (Nat.totient m) < (cyclotomic m ℝ).eval (y ^ p) := hlow
    _ = (cyclotomic (m * p) ℝ).eval y * (cyclotomic m ℝ).eval y := key
    _ ≤ (cyclotomic (m * p) ℝ).eval y * (y + 1) ^ (Nat.totient m) := by
        have hmp : 0 < (cyclotomic (m * p) ℝ).eval y := by
          rcases lt_trichotomy ((cyclotomic (m * p) ℝ).eval y) 0 with h | h | h
          · nlinarith [hlow, key, pow_pos (show (0:ℝ) < y ^ p - 1 by linarith) (Nat.totient m)]
          · nlinarith [hlow, key, pow_pos (show (0:ℝ) < y ^ p - 1 by linarith) (Nat.totient m)]
          · exact h
        nlinarith

