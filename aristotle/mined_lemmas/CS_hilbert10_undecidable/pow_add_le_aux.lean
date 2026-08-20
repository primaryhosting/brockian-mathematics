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

theorem pow_add_le_aux (b c : ℕ) :
    ∀ k : ℕ, (b + c) ^ (k + 1) ≤ b ^ (k + 1) + (k + 1) * c * (b + c) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc (b + c) ^ (k + 2) = (b + c) * (b + c) ^ (k + 1) := by ring
        _ ≤ (b + c) * (b ^ (k + 1) + (k + 1) * c * (b + c) ^ k) := Nat.mul_le_mul_left _ ih
        _ = b ^ (k + 2) + c * b ^ (k + 1) + (k + 1) * c * ((b + c) * (b + c) ^ k) := by ring
        _ ≤ b ^ (k + 2) + c * (b + c) ^ (k + 1) + (k + 1) * c * (b + c) ^ (k + 1) := by
            gcongr
            · exact Nat.le_add_right _ _
            · exact le_of_eq (by ring)
        _ = b ^ (k + 2) + (k + 2) * c * (b + c) ^ (k + 1) := by ring

/-- If `u` is large compared with `r`, then `r ! = u ^ r / u.choose r`. -/
