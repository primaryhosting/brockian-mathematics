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

lemma lt_cyclotomic_mul_prime_eval {p m y : ℕ} (hp : p.Prime) (hmp : m ∣ p - 1) (hy : 2 ≤ y)
    (hexc : ¬ (y = 2 ∧ m = 2 ∧ p = 3)) : (p : ℤ) < (cyclotomic (m * p) ℤ).eval (y : ℤ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmp (by omega)
  have hmle : m ≤ p - 1 := Nat.le_of_dvd (by omega) hmp
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have : m = 1 := by omega
    rw [this, one_mul]
    exact lt_cyclotomic_prime_eval hp hy
  · -- `2 ≤ m`, so `p ≥ 3`
    have hp3 : 3 ≤ p := by omega
    have hpm : ¬ p ∣ m := Nat.not_dvd_of_pos_of_lt hm0 (by omega)
    rcases eq_or_lt_of_le hp3 with hp3' | hp4
    · -- `p = 3`, hence `m = 2` and `y ≥ 3`
      have hm2' : m = 2 := by omega
      have hy3 : 3 ≤ y := by
        rcases eq_or_lt_of_le hy with h | h
        · exact absurd ⟨h.symm, hm2', hp3'.symm⟩ hexc
        · omega
      have hmp6 : m * p = 6 := by rw [hm2', ← hp3']
      rw [hmp6, cyclotomic_six]
      have : (3 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy3
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
      rw [← hp3']
      push_cast
      nlinarith
    · -- `p ≥ 5`
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p
          · exact absurd hp (by decide)
        · exact h
      exact lt_cyclotomic_mul_prime_eval_of_five hp hp5 hm2 hpm hy

/-- The size bound at the level of `n = p ^ k * m`. -/
