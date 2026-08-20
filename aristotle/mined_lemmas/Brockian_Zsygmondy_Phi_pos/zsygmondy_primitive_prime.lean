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

theorem zsygmondy_primitive_prime (a n : ℕ) (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hexc : ¬ (a = 2 ∧ n = 6)) :
    ∃ p, p.Prime ∧ p ∣ (a ^ n - 1) ∧ ∀ m, 0 < m → m < n → ¬ p ∣ (a ^ m - 1) := by
  have hn0 : 0 < n := by omega
  have hn2 : 2 < n := by omega
  have hPpos : 0 < Phi n a := Phi_pos hn2 a
  have hP1 : 1 < Phi n a := one_lt_Phi hn2 ha
  set N : ℕ := (Phi n a).toNat with hNdef
  have hNcast : (N : ℤ) = Phi n a := Int.toNat_of_nonneg hPpos.le
  have hN1 : 1 < N := by omega
  have hdvdN : ∀ q : ℕ, ((q : ℤ) ∣ Phi n a ↔ q ∣ N) := by
    intro q
    rw [← hNcast]
    exact Int.natCast_dvd_natCast
  by_cases hcase : ∃ q, q.Prime ∧ q ∣ N ∧ ¬ q ∣ n
  · obtain ⟨q, hq, hqN, hqn⟩ := hcase
    have hqP : (q : ℤ) ∣ Phi n a := (hdvdN q).2 hqN
    have hord : orderOf ((a : ZMod q)) = n := orderOf_eq_of_not_dvd hq hqn hqP
    refine ⟨q, hq, ?_, not_dvd_of_orderOf_eq (by omega) hord⟩
    have h1 : (q : ℤ) ∣ (a : ℤ) ^ n - 1 := hqP.trans (Phi_dvd n a)
    have hle : 1 ≤ a ^ n := Nat.one_le_pow _ _ (by omega)
    have hcast : ((a ^ n - 1 : ℕ) : ℤ) = (a : ℤ) ^ n - 1 := by
      push_cast [hle]
      ring
    exact_mod_cast hcast ▸ h1
  · exfalso
    push_neg at hcase
    obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
    have hpP : (p : ℤ) ∣ Phi n a := (hdvdN p).2 hpN
    have hpn : p ∣ n := hcase p hp hpN
    have hk0 : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0.ne' hpn
    have hnk : p ^ (n.factorization p) * (n / p ^ (n.factorization p)) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hmp : n / p ^ (n.factorization p) ∣ p - 1 := ordCompl_dvd_pred hn0 hp hpn hpP
    have huniq : ∀ q, q.Prime → q ∣ N → q = p := by
      intro q hq hqN
      have hqn : q ∣ n := hcase q hq hqN
      have h1 : q ≤ p := prime_le_of_dvd_Phi hn0 hp hpn hpP q hq hqn
      have h2 : p ≤ q := prime_le_of_dvd_Phi hn0 hq hqn ((hdvdN q).2 hqN) p hp hpn
      omega
    have hsq : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := not_sq_dvd_Phi ha hn2 hp hpn hpP
    have hNp : N = p := by
      obtain ⟨t, ht⟩ := hpN
      have ht1 : t = 1 := by
        by_contra hne
        have ht0 : t ≠ 0 := by
          rintro rfl
          simp at ht
          omega
        obtain ⟨r, hr, hrt⟩ := Nat.exists_prime_and_dvd hne
        have hrN : r ∣ N := ht ▸ hrt.mul_left p
        have hrp : r = p := huniq r hr hrN
        subst hrp
        obtain ⟨s, hs⟩ := hrt
        refine hsq ⟨(s : ℤ), ?_⟩
        rw [← hNcast, ht, hs]
        push_cast
        ring
      rw [ht, ht1, mul_one]
    have hlt := lt_Phi ha hp hk0 hmp hnk.symm hexc
    rw [← hNcast, hNp] at hlt
    omega

end Brockian.Zsygmondy

