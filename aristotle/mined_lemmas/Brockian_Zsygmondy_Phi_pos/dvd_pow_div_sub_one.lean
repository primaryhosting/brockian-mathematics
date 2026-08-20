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

lemma dvd_pow_div_sub_one {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : (p : ℤ) ∣ (a : ℤ) ^ (n / p) - 1 := by
  set k := n.factorization p with hk_def
  set m := n / p ^ k with hm_def
  have hmk : n = p ^ k * m := by rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (by
    intro heq
    rw [heq, Nat.mul_zero] at hmk
    exact hn.ne' hmk)
  have hpndiv : ¬ p ∣ m := by
    rw [hm_def]
    rw [Nat.Prime.dvd_iff_one_le_factorization hp]
    · rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
      simp [hp.factorization_self]
    · omega
  rw [hmk] at hdvd
  have hord : orderOf (a : ZMod p) = m := orderOf_eq_of_dvd hp hpndiv hdvd
  have hk_pos : k > 0 := hp.factorization_pos_of_dvd hn.ne' hpn
  have hdiv : m ∣ n / p := by
    rw [hmk]
    have hpdiv : p ∣ p ^ k := dvd_pow_self p hk_pos.ne'
    have heq : p ^ k * m / p = p ^ (k - 1) * m := by
      have : p ^ k * m = p * (p ^ (k - 1) * m) := by
        rw [← mul_assoc]
        rw [show p ^ k = p * p ^ (k - 1) by rw [← pow_succ', Nat.sub_add_cancel hk_pos]]
      rw [this, Nat.mul_div_cancel_left _ hp.pos]
    rw [heq]
    exact dvd_mul_left m _
  have hpow_eq_one : (a : ZMod p) ^ (n / p) = 1 := by
    have hdiv' : orderOf (a : ZMod p) ∣ n / p := hord ▸ hdiv
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv'
  have hsub : ((a : ℕ) ^ (n / p) : ZMod p) - 1 = 0 := by simp [hpow_eq_one]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [hsub]

/-! ### The square of `p` does not divide `Φ n a` -/

/-- Lifting the exponent: for an odd prime `p ∣ n` we have `p ^ 2 ∤ Φ n a`. -/
