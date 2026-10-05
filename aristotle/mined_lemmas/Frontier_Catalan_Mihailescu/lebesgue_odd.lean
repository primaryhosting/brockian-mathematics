import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

theorem lebesgue_odd {r : ℕ} (hodd : Odd r) (hr : 3 ≤ r) (x y : ℕ) (hy : 0 < y) :
    x ^ r ≠ y ^ 2 + 1 := by
  intro h
  -- `y` is even
  have hyeven : Even y := by
    rcases Nat.even_or_odd y with he | ho
    · exact he
    obtain ⟨m, hm⟩ := ho
    exfalso
    subst hm
    obtain ⟨u, hu⟩ := Nat.even_mul_succ_self m
    have hexp : (2 * m + 1) ^ 2 + 1 = 8 * u + 2 := by
      have h1 : (2 * m + 1) ^ 2 + 1 = 4 * (m * (m + 1)) + 2 := by ring
      rw [hu] at h1; omega
    have hdvd2 : 2 ∣ x ^ r := ⟨4 * u + 1, by rw [h, hexp]; ring⟩
    have h2x : 2 ∣ x := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd2
    obtain ⟨c, rfl⟩ := h2x
    have h8 : (8 : ℕ) ∣ (2 * c) ^ r := by
      have h1 : (2:ℕ) ^ 3 ∣ 2 ^ r := pow_dvd_pow 2 hr
      have h2 : (2:ℕ) ^ r ∣ (2 * c) ^ r := ⟨c ^ r, by rw [mul_pow]⟩
      exact dvd_trans (by norm_num) (dvd_trans h1 h2)
    rw [h, hexp] at h8
    omega
  -- `x` is odd
  have hxodd : Odd x := by
    have hy2 : Even (y ^ 2) := Nat.even_pow.mpr ⟨hyeven, two_ne_zero⟩
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have hev : Even (x ^ r) := Nat.even_pow.mpr ⟨he, by omega⟩
      rw [Nat.even_iff] at hev hy2
      omega
    · exact ho
  -- pass to the Gaussian integers
  have hZ : (x : ℤ) ^ r = (y : ℤ) ^ 2 + 1 := by exact_mod_cast congrArg (Nat.cast (R := ℤ)) h
  have hYeven : Even ((y : ℤ)) := by exact_mod_cast hyeven
  set X : ℤ := (x : ℤ) with hXdef
  set Y : ℤ := (y : ℤ) with hYdef
  set s : GaussianInt := ⟨Y, 1⟩ with hs
  set t : GaussianInt := ⟨Y, -1⟩ with ht
  have hst : s * t = ((X : GaussianInt)) ^ r := by
    have h1 : s * t = (((Y ^ 2 + 1 : ℤ)) : GaussianInt) := by
      simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast]
      constructor <;> ring
    rw [h1, ← hZ]; push_cast; ring
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' (gauss_coprime hYeven) hst
  have hu4 : ((u : GaussianInt)) ^ 4 = 1 := unit_pow_four u.isUnit
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨w, hw⟩ := Nat.even_mul_succ_self m
  have hr2 : r * r = 8 * w + 1 := by
    subst hm
    have h1 : (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
    rw [hw] at h1; omega
  set z : GaussianInt := ((u : GaussianInt)) ^ r * d with hzdef
  have hz : z ^ r = s := by
    have h1 : z ^ r = ((u : GaussianInt)) ^ (r * r) * d ^ r := by
      rw [hzdef, mul_pow, ← pow_mul]
    rw [h1, hr2]
    have h8 : ((u : GaussianInt)) ^ (8 * w + 1) = (u : GaussianInt) := by
      have h2 : ((u : GaussianInt)) ^ 8 = 1 := by
        rw [show (8:ℕ) = 4 * 2 by norm_num, pow_mul, hu4, one_pow]
      rw [pow_add, pow_one, pow_mul, h2, one_pow, one_mul]
    rw [h8, mul_comm]
    exact hu
  have hodd' : Odd r := ⟨m, hm⟩
  have hstar : (star z) ^ r = t := by
    rw [← star_pow, hz, hs, ht]
    apply Zsqrtd.ext <;> simp
  -- the imaginary part of `z` is `±1`
  have hsubst : s - t = (⟨0, 2⟩ : GaussianInt) := by
    rw [hs, ht]; apply Zsqrtd.ext <;> simp <;> ring
  have hzs : z - star z = (⟨0, 2 * z.im⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp <;> ring
  have hdvd : (⟨0, 2 * z.im⟩ : GaussianInt) ∣ (⟨0, 2⟩ : GaussianInt) := by
    have h1 := sub_dvd_pow_sub_pow z (star z) r
    rw [hz, hstar, hsubst, hzs] at h1
    exact h1
  obtain ⟨c, hc⟩ := hdvd
  have hnormdvd : (4 * z.im ^ 2 : ℤ) ∣ 4 := by
    refine ⟨c.norm, ?_⟩
    have h1 := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul] at h1
    simp only [Zsqrtd.norm_def] at h1 ⊢
    linarith [h1]
  have hb : z.im = 1 ∨ z.im = -1 := by
    have h1 : (4:ℤ) * z.im ^ 2 ∣ 4 * 1 := by simpa using hnormdvd
    have h2 : z.im ^ 2 ∣ 1 := (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp h1
    have h3 : z.im ∣ 1 := dvd_trans (dvd_pow_self z.im two_ne_zero) h2
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one h3)
  -- the real part of `z` is even and nonzero
  have hnormz : z.norm = z.re ^ 2 + 1 := by
    rcases hb with h1 | h1 <;> rw [Zsqrtd.norm_def, h1] <;> ring
  have hnorms : s.norm = X ^ r := by rw [hs, Zsqrtd.norm_def, hZ]; ring
  have hpow : (z.re ^ 2 + 1) ^ r = X ^ r := by rw [← hnormz, ← znorm_pow, hz, hnorms]
  have hXeq : z.re ^ 2 + 1 = X := (Odd.strictMono_pow (R := ℤ) hodd').injective hpow
  have hXodd : Odd X := by rw [hXdef]; exact_mod_cast hxodd
  have hare : Even z.re := by
    rcases Int.even_or_odd z.re with he | ho
    · exact he
    · exfalso
      obtain ⟨k, hk⟩ := ho
      obtain ⟨j, hj⟩ := hXodd
      rw [hk] at hXeq
      have h1 : X = 2 * (2 * (k * k + k) + 1) := by rw [← hXeq]; ring
      generalize (k * k + k) = n at h1
      omega
  have hne : z.re ≠ 0 := by
    intro h0
    rw [h0] at hXeq
    have hX1 : X = 1 := by omega
    rw [hX1, one_pow] at hZ
    have hY0 : Y = 0 := by nlinarith [sq_nonneg Y]
    rw [hYdef] at hY0
    omega
  -- conclude with the key lemma
  rcases hb with h1 | h1
  · have hzeq : ((z.re : GaussianInt)) + gi = z := by
      apply Zsqrtd.ext <;> simp [gi, h1]
    have him : ((((z.re : GaussianInt)) + gi) ^ r).im = 1 := by rw [hzeq, hz, hs]
    exact im_pow_add_gi_ne_pm_one hodd' hr hare hne (Or.inl rfl) him
  · have hzeq : ((z.re : GaussianInt)) + gi = star z := by
      apply Zsqrtd.ext <;> simp [gi, h1]
    have him : ((((z.re : GaussianInt)) + gi) ^ r).im = -1 := by rw [hzeq, hstar, ht]
    exact im_pow_add_gi_ne_pm_one hodd' hr hare hne (Or.inr rfl) him

/-- **Lebesgue's theorem (1850)**: for `p ≥ 2` and `y ≥ 1`, `x ^ p = y ^ 2 + 1` is impossible;
that is, `1` is never the difference of a perfect power and a nonzero perfect square. -/
