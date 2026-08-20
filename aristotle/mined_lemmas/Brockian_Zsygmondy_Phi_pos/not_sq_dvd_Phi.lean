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

lemma not_sq_dvd_Phi {n a p : ℕ} (ha : 2 ≤ a) (hn : 2 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := by
  have hn0 : 0 < n := by omega
  by_cases hp2 : p = 2
  · subst hp2
    -- here `n` is a power of two, and `Φ n a = a ^ (2 ^ (k - 1)) + 1 ≡ 2 [MOD 4]`
    have hmp : n / 2 ^ (n.factorization 2) ∣ 1 := ordCompl_dvd_pred hn0 hp hpn hdvd
    have hm1 : n / 2 ^ (n.factorization 2) = 1 := Nat.dvd_one.1 hmp
    have hnk : 2 ^ (n.factorization 2) = n := by
      have := Nat.ordProj_mul_ordCompl_eq_self n 2
      rw [hm1, mul_one] at this
      exact this
    have hk2 : 2 ≤ n.factorization 2 := by
      by_contra hlt
      interval_cases h : n.factorization 2 <;> omega
    obtain ⟨j, hj⟩ : ∃ j, n.factorization 2 = j + 1 + 1 := ⟨n.factorization 2 - 2, by omega⟩
    rw [hj] at hnk
    have hPhi : Phi n a = ((a : ℤ) ^ (2 ^ j)) ^ 2 + 1 := by
      unfold Phi
      rw [← hnk, cyclotomic_two_pow_eval (j + 1) (a : ℤ), ← pow_mul, pow_succ, mul_comm (2 ^ j) 2]
    rw [hPhi]
    have : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
    rw [this]
    exact not_four_dvd_sq_add_one _
  · exact not_sq_dvd_Phi_of_odd ha hn0 hp hp2 hpn (dvd_pow_div_sub_one hn0 hp hpn hdvd)

/-! ### The size bound `Φ n a > p` -/

/-- `Φ_{p^(k+1) m}(x) = Φ_{m p}(x ^ (p ^ k))`. -/
