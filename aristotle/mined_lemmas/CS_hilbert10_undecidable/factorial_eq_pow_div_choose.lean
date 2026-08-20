import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

theorem factorial_eq_pow_div_choose (r u : ℕ) (hr : 1 ≤ r) (h1 : 2 ^ r * r ! * r ^ 2 < u)
    (h2 : 2 * r ≤ u) : r ! = u ^ r / u.choose r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  set r := k + 1 with hrdef
  set w := u - r with hw
  have hur : r ≤ u := by omega
  have huw : u = w + r := by omega
  have hww : u ≤ 2 * w := by omega
  have hupos : 0 < u := by omega
  have hC : 0 < u.choose r := Nat.choose_pos hur
  have hD : u.descFactorial r = r ! * u.choose r := Nat.descFactorial_eq_factorial_mul_choose u r
  have hDle : r ! * u.choose r ≤ u ^ r := hD ▸ Nat.descFactorial_le_pow u r
  have hwD : w ^ r ≤ r ! * u.choose r := by
    rw [← hD]
    calc w ^ r ≤ (u + 1 - r) ^ r := Nat.pow_le_pow_left (by omega) _
      _ ≤ u.descFactorial r := Nat.pow_sub_le_descFactorial u r
  have hkey : r ! * r ^ 2 * u ^ k < w ^ r := by
    have e1 : 2 ^ r * (r ! * r ^ 2) * u ^ k < u * u ^ k := by
      have h3 : 2 ^ r * r ! * r ^ 2 * u ^ k < u * u ^ k :=
        Nat.mul_lt_mul_of_pos_right h1 (pow_pos hupos k)
      calc 2 ^ r * (r ! * r ^ 2) * u ^ k = 2 ^ r * r ! * r ^ 2 * u ^ k := by ring
        _ < u * u ^ k := h3
    have e2 : u * u ^ k ≤ 2 ^ r * w ^ r := by
      calc u * u ^ k = u ^ r := by rw [hrdef]; ring
        _ ≤ (2 * w) ^ r := Nat.pow_le_pow_left hww r
        _ = 2 ^ r * w ^ r := by rw [Nat.mul_pow]
    have h4 : 2 ^ r * (r ! * r ^ 2 * u ^ k) < 2 ^ r * w ^ r := by
      calc 2 ^ r * (r ! * r ^ 2 * u ^ k) = 2 ^ r * (r ! * r ^ 2) * u ^ k := by ring
        _ < u * u ^ k := e1
        _ ≤ 2 ^ r * w ^ r := e2
    exact lt_of_mul_lt_mul_left h4 (Nat.zero_le _)
  have hpow : u ^ r ≤ w ^ r + r * r * u ^ k := by
    calc u ^ r = (w + r) ^ (k + 1) := by rw [huw]
      _ ≤ w ^ (k + 1) + (k + 1) * r * (w + r) ^ k := pow_add_le_aux w r k
      _ = w ^ r + r * r * u ^ k := by rw [← huw, hrdef]
  have hstrict : r ! * u ^ r < (r ! + 1) * (r ! * u.choose r) := by
    calc r ! * u ^ r ≤ r ! * (w ^ r + r * r * u ^ k) := Nat.mul_le_mul_left _ hpow
      _ = r ! * w ^ r + r ! * (r * r) * u ^ k := by ring
      _ < r ! * w ^ r + w ^ r := by
          have h5 : r ! * (r * r) * u ^ k = r ! * r ^ 2 * u ^ k := by ring
          omega
      _ ≤ r ! * (r ! * u.choose r) + r ! * u.choose r := by
          have h3 : r ! * w ^ r ≤ r ! * (r ! * u.choose r) := Nat.mul_le_mul_left _ hwD
          omega
      _ = (r ! + 1) * (r ! * u.choose r) := by ring
  have hlt : u ^ r < (r ! + 1) * u.choose r := by
    have h6 : r ! * u ^ r < r ! * ((r ! + 1) * u.choose r) := by
      calc r ! * u ^ r < (r ! + 1) * (r ! * u.choose r) := hstrict
        _ = r ! * ((r ! + 1) * u.choose r) := by ring
    exact lt_of_mul_lt_mul_left h6 (Nat.zero_le _)
  have hge : r ! ≤ u ^ r / u.choose r := (Nat.le_div_iff_mul_le hC).2 hDle
  have hle : u ^ r / u.choose r < r ! + 1 := (Nat.div_lt_iff_lt_mul hC).2 hlt
  omega

/-- An explicit formula for the factorial in terms of a binomial coefficient. -/
