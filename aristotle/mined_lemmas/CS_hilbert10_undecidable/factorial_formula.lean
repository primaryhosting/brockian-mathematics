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

theorem factorial_formula (r : ℕ) :
    r ! = ((2 * r) ^ (r + 2) + 2 * r + 1) ^ r / (((2 * r) ^ (r + 2) + 2 * r + 1).choose r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · refine factorial_eq_pow_div_choose r _ hr ?_ (by omega)
    have hfac : r ! ≤ r ^ r := Nat.factorial_le_pow r
    have h1 : 2 ^ r * r ! * r ^ 2 ≤ (2 * r) ^ r * r ^ 2 := by
      have h : 2 ^ r * r ! ≤ 2 ^ r * r ^ r := Nat.mul_le_mul_left _ hfac
      calc 2 ^ r * r ! * r ^ 2 ≤ 2 ^ r * r ^ r * r ^ 2 := Nat.mul_le_mul_right _ h
        _ = (2 * r) ^ r * r ^ 2 := by rw [Nat.mul_pow]
    have h2 : (2 * r) ^ r * r ^ 2 ≤ (2 * r) ^ (r + 2) := by
      calc (2 * r) ^ r * r ^ 2 ≤ (2 * r) ^ r * (2 * r) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
        _ = (2 * r) ^ (r + 2) := by rw [← pow_add]
    omega

open Dioph in
/-- **The factorial is a Diophantine function.** -/
