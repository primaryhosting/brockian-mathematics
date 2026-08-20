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

lemma not_sq_dvd_Phi_of_odd {n a p : ℕ} (ha : 2 ≤ a) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hdvd : (p : ℤ) ∣ (a : ℤ) ^ (n / p) - 1) : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := by
  intro hsq
  unfold Phi at hsq
  set q := n / p with hq
  have hpq : p * q = n := Nat.mul_div_cancel' hpn
  have hp2' := hp.two_le
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hpq; omega
    · exact h
  have hqn : q ∈ n.properDivisors := by
    refine Nat.mem_properDivisors.2 ⟨⟨p, by rw [← hpq]; ring⟩, ?_⟩
    nlinarith [hpq, hq0]
  have hdvd2 : ((a : ℤ) ^ q - 1) * (cyclotomic n ℤ).eval (a : ℤ) ∣ (a : ℤ) ^ n - 1 := by
    obtain ⟨c, hc⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hqn
    refine ⟨c.eval (a : ℤ), ?_⟩
    have := congrArg (Polynomial.eval (a : ℤ)) hc
    simpa using this
  set x : ℤ := (a : ℤ) ^ q with hx
  have hx2 : 2 ≤ x := by
    calc (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      _ = (a : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (a : ℤ) ^ q := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ a)) (by omega)
  have hxp : (a : ℤ) ^ n = x ^ p := by rw [hx, ← pow_mul, mul_comm q p, hpq]
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro h
    have h1 : (p : ℤ) ∣ 1 := (dvd_sub_right h).mp (by simpa using hdvd)
    have := Int.le_of_dvd one_pos h1
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2'
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd hdvd hpx p
  rw [one_pow, hp.emultiplicity_self] at hlte
  have hdvd3 : (x - 1) * (p : ℤ) ^ 2 ∣ x ^ p - 1 := by
    obtain ⟨c, hc⟩ := hsq
    obtain ⟨d, hd⟩ := hdvd2
    exact ⟨c * d, by rw [← hxp, hd, hc]; ring⟩
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : emultiplicity (p : ℤ) ((x - 1) * (p : ℤ) ^ 2)
      = emultiplicity (p : ℤ) (x - 1) + 2 := by
    rw [emultiplicity_mul hprime, emultiplicity_pow_self hprime.ne_zero hprime.not_unit]
    norm_num
  have h1 : emultiplicity (p : ℤ) ((x - 1) * (p : ℤ) ^ 2) ≤ emultiplicity (p : ℤ) (x ^ p - 1) :=
    emultiplicity_le_emultiplicity_of_dvd_right hdvd3
  rw [h2, hlte] at h1
  have hfin : FiniteMultiplicity (p : ℤ) (x - 1) :=
    FiniteMultiplicity.of_prime_left hprime (by intro h; omega)
  rw [hfin.emultiplicity_eq_multiplicity] at h1
  set M := multiplicity (p : ℤ) (x - 1) with hM
  have h3 : ((M + 2 : ℕ) : ℕ∞) ≤ ((M + 1 : ℕ) : ℕ∞) := by push_cast; exact h1
  have h4 := Nat.cast_le (α := ℕ∞).mp h3
  omega

