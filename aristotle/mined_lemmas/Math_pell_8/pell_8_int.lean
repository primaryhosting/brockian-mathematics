/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`), namely `(x, y) = (3, 1)`, since `3² - 8·1² = 9 - 8 = 1`. -/

theorem pell_8_int : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by norm_num, one_ne_zero⟩

/-- The same statement over `ℕ`, obtained from Mathlib's Pell machinery:
`Pell.pell_eq` says `xn a1 n * xn a1 n - (a² - 1) * yn a1 n * yn a1 n = 1`,
and for `a = 3` the parameter is `d = 3² - 1 = 8`. -/
