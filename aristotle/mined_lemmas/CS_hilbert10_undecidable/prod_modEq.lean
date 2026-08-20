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

theorem prod_modEq (y t M r : ℕ) (h : t * r = (t - 1) * M + 1) :
    (t ^ y * ∏ i ∈ range y, (r + 1 + i)) ≡ ∏ i ∈ range y, (1 + (i + 1) * t) [MOD M] := by
  induction y with
  | zero => simp; rfl
  | succ y ih =>
      have step : t * (r + 1 + y) ≡ 1 + (y + 1) * t [MOD M] := by
        have heq : t * (r + 1 + y) = 1 + (y + 1) * t + M * (t - 1) := by
          have h2 : t * (r + 1 + y) = t * r + t + t * y := by ring
          rw [h2, h]; ring
        show _ % M = _ % M
        rw [heq, Nat.add_mul_mod_self_left]
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
      calc t ^ y * t * ((∏ i ∈ range y, (r + 1 + i)) * (r + 1 + y))
          = (t ^ y * ∏ i ∈ range y, (r + 1 + i)) * (t * (r + 1 + y)) := by ring
        _ ≡ (∏ i ∈ range y, (1 + (i + 1) * t)) * (1 + (y + 1) * t) [MOD M] := ih.mul step

