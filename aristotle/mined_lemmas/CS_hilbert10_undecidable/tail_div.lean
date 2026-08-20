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

theorem tail_div (u : ℕ) (hu : 1 < u) (a : ℕ → ℕ) (ha : ∀ i, a i < u) (m : ℕ) :
    ∀ k ≤ m, (∑ i ∈ range m, a i * u ^ i) / u ^ k = ∑ i ∈ range (m - k), a (k + i) * u ^ i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hstep := tail_step u a m k (by omega)
      rw [pow_succ, ← Nat.div_div_eq_div_mul, h1, hstep,
        Nat.add_mul_div_left _ _ (by omega : 0 < u), Nat.div_eq_of_lt (ha k)]
      have hmk : m - (k + 1) = m - k - 1 := by omega
      rw [hmk]
      omega

/-- Extraction of the `k`-th digit in base `u`. -/
