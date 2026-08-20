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

lemma lt_cyclotomic_mul_prime_eval_of_five {p m y : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 2 ≤ m)
    (hpm : ¬ p ∣ m) (hy : 2 ≤ y) : (p : ℤ) < (cyclotomic (m * p) ℤ).eval (y : ℤ) := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have h1 : (p : ℝ) ≤ ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1) := real_base_bound hp5 hyR
  have hbase1 : (1 : ℝ) ≤ ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    linarith
  have hphi : Nat.totient m ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  have h2 : ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1)
      ≤ (((y : ℝ) ^ p - 1) / ((y : ℝ) + 1)) ^ (Nat.totient m) := le_self_pow₀ hbase1 hphi
  have h3 := real_lower_bound hm hp hpm hyR
  have h4 : (p : ℝ) < (cyclotomic (m * p) ℝ).eval (y : ℝ) := by linarith
  have h5 : (cyclotomic (m * p) ℝ).eval ((y : ℤ) : ℝ)
      = (((cyclotomic (m * p) ℤ).eval (y : ℤ) : ℤ) : ℝ) := by
    simpa using cyclotomic.eval_apply ((y : ℤ)) (m * p) (Int.castRingHom ℝ)
  rw [show ((y : ℕ) : ℝ) = (((y : ℤ)) : ℝ) by push_cast; ring, h5] at h4
  exact_mod_cast h4

/-- The key size bound: `Φ_{m p}(y) > p`, where `m ∣ p - 1` and `y ≥ 2`, except in the
single case `y = 2, m = 2, p = 3` (which is `Φ₆(2) = 3`). -/
