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

theorem prod_le_pow (y t : ℕ) : ∏ i ∈ range y, (1 + (i + 1) * t) ≤ (1 + y * t) ^ y := by
  calc ∏ i ∈ range y, (1 + (i + 1) * t) ≤ ∏ _i ∈ range y, (1 + y * t) := by
        refine Finset.prod_le_prod' ?_
        intro i hi
        have : i + 1 ≤ y := by simpa using hi
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) 1
    _ = (1 + y * t) ^ y := by simp

/-- An explicit formula for `∏_{k=1}^{y} (1 + k * t)`, obtained by inverting `t` modulo a
large modulus coprime to `t`. -/
