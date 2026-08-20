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

lemma ordCompl_dvd_pred {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : n / p ^ (n.factorization p) ∣ p - 1 := by
  set k := n.factorization p
  set m := n / p ^ k
  have hnk : n = p ^ k * m := by
    rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)]
  have hdiv : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hle : p ^ k ≤ n := Nat.le_of_dvd hn hdiv
  have hm_pos : 0 < m := Nat.div_pos hle (pow_pos hp.pos k)
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
  have hpm : ¬ p ∣ m := by
    rw [Nat.dvd_div_iff_mul_dvd hdiv]
    intro h
    have h2 : p ^ (k + 1) ∣ n := by simpa [pow_succ] using h
    have hfac := Nat.factorization_le_iff_dvd (pow_ne_zero (k + 1) hp.ne_zero) hn.ne' |>.mpr h2
    have hpk := hfac p
    simp only [Nat.factorization_pow, Finsupp.smul_apply] at hpk
    rw [Nat.Prime.factorization_self hp] at hpk
    convert hpk using 1
    simp [k]
  have hdvd' : (p : ℤ) ∣ Phi (p ^ k * m) a := by rw [← hnk]; exact hdvd
  have hord := orderOf_eq_of_dvd hp hpm hdvd'
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hm1 : m = 1
  · simp [hm1]
  · -- Otherwise, we can prove a ≢ 0 (mod p)
    have ha_ne : (a : ZMod p) ≠ 0 := by
      intro ha
      have hroot := isRoot_zmod_of_dvd_Phi hdvd
      rw [Polynomial.IsRoot] at hroot
      have heq : (cyclotomic n (ZMod p)).eval ((a : ZMod p)) = (cyclotomic n (ZMod p)).eval 0 := by
        rw [ha]
      rw [heq] at hroot
      have hn1 : 1 < n := by
        by_contra hle1
        push_neg at hle1
        interval_cases n
        simp [Phi] at hdvd
        · -- n = 1: p ∣ a - 1 and p ∣ a implies p ∣ 1
          have hpa : (p : ℤ) ∣ a := by
            have := ZMod.intCast_zmod_eq_zero_iff_dvd a p
            simp [ha] at this
            exact this
          have : (p : ℤ) ∣ 1 := by simpa using Int.dvd_sub hpa hdvd
          exact Nat.Prime.not_dvd_one hp (Int.natCast_dvd_natCast.mp this)
      have hcoeff := Polynomial.cyclotomic_coeff_zero (ZMod p) hn1
      have hroot' : (cyclotomic n (ZMod p)).coeff 0 = 0 := by
        simp [Polynomial.eval_eq_sum_range, Finset.sum_range_succ'] at hroot
        exact hroot
      rw [hcoeff] at hroot'
      norm_num at hroot'
    have key : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha_ne
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr key

/-- If `p ∣ n` and `p ∣ Φ n a`, then every prime factor of `n` is at most `p`. -/
