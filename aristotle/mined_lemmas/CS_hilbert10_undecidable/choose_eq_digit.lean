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

theorem choose_eq_digit (n k : ℕ) :
    n.choose k = (2 ^ n + 2) ^ n / (2 ^ n + 1) ^ k % (2 ^ n + 1) := by
  set u := 2 ^ n + 1 with hudef
  have hu : 1 < u := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have ha : ∀ i, n.choose i < u := fun i => lt_of_le_of_lt (Nat.choose_le_two_pow n i) (by omega)
  have hexp : (2 ^ n + 2) ^ n = ∑ i ∈ range (n + 1), n.choose i * u ^ i := by
    have h : (2 : ℕ) ^ n + 2 = u + 1 := by omega
    rw [h, add_pow]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rcases lt_or_ge k (n + 1) with hk | hk
  · rw [hexp, digit_extract u hu _ ha (n + 1) k hk]
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hlt : (2 ^ n + 2) ^ n < u ^ (n + 1) := by
      rw [hexp]; exact sum_digits_lt u _ ha (n + 1)
    have hle : u ^ (n + 1) ≤ u ^ k := Nat.pow_le_pow_right (by omega) hk
    rw [h0, Nat.div_eq_of_lt (lt_of_lt_of_le hlt hle)]
    simp

open Dioph in
/-- **Binomial coefficients are Diophantine.** -/
