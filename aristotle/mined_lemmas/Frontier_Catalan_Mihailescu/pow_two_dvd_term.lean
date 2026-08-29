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

lemma pow_two_dvd_term {r j v e : ℕ} (hv : 1 ≤ v) (hj : 2 ≤ j)
    (he : 2 ^ e ∣ r.choose 2) :
    2 ^ (2 * v + e + 1) ∣ r.choose (2 * j) * 2 ^ (2 * j * v) := by
  obtain ⟨t, j', hj', hjt⟩ := Nat.exists_eq_two_pow_mul_odd (n := j) (by omega)
  have hdvd : 2 ^ e ∣ r.choose (2 * j) * j := pow_two_dvd_choose_mul hj he
  have hcop : Nat.Coprime (2 ^ e) j' := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hj'
    omega
  have hdvd2 : 2 ^ e ∣ r.choose (2 * j) * 2 ^ t := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [mul_assoc, ← hjt]
    exact hdvd
  have htj : 2 ^ t ≤ j := Nat.le_of_dvd (by omega) ⟨j', hjt⟩
  have htlt : t < 2 ^ t := Nat.lt_two_pow_self
  have ht1 : t + 1 ≤ j := by omega
  have hineq : 2 * v + e + 1 ≤ e + (2 * j * v - t) := by
    have h2 : 2 * j * v = 2 * v * (j - 1) + 2 * v := by
      have hj1 : j - 1 + 1 = j := by omega
      nlinarith [hj1]
    have h1 : 2 * (j - 1) ≤ 2 * v * (j - 1) := by nlinarith [Nat.sub_le j 1]
    omega
  have hsum : t + (2 * j * v - t) = 2 * j * v := by
    have hle : t ≤ 2 * j * v := by nlinarith
    omega
  have h2 : 2 ^ e * 2 ^ (2 * j * v - t) ∣ (r.choose (2 * j) * 2 ^ t) * 2 ^ (2 * j * v - t) :=
    mul_dvd_mul_right hdvd2 _
  have h3 : (r.choose (2 * j) * 2 ^ t) * 2 ^ (2 * j * v - t)
      = r.choose (2 * j) * 2 ^ (2 * j * v) := by
    rw [mul_assoc (r.choose (2 * j)) (2 ^ t), ← pow_add, hsum]
  have h4 : (2:ℕ) ^ e * 2 ^ (2 * j * v - t) = 2 ^ (e + (2 * j * v - t)) := (pow_add 2 _ _).symm
  rw [h3, h4] at h2
  exact dvd_trans (pow_dvd_pow 2 hineq) h2

/-- For `a` even and nonzero and `r ≥ 3` odd, `(a + i) ^ r` cannot have imaginary part `±1`.

The imaginary part is `±(1 - C(r,2) a² + C(r,4) a⁴ - ⋯)`; reduction mod `4` forces the
alternating tail `- C(r,2) a² + C(r,4) a⁴ - ⋯` to vanish, which is impossible because the
term `C(r,2) a²` has strictly smaller `2`-adic valuation than all the later ones. -/
