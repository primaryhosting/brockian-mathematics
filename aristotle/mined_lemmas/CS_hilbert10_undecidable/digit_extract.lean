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

theorem digit_extract (u : ℕ) (hu : 1 < u) (a : ℕ → ℕ) (ha : ∀ i, a i < u) (m k : ℕ)
    (hk : k < m) : (∑ i ∈ range m, a i * u ^ i) / u ^ k % u = a k := by
  rw [tail_div u hu a ha m k (le_of_lt hk), tail_step u a m k hk,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha k)]

/-! ## Binomial coefficients are Diophantine -/

/-- `n.choose k` is the `k`-th digit of `(u + 1) ^ n` in base `u = 2 ^ n + 1`. -/
