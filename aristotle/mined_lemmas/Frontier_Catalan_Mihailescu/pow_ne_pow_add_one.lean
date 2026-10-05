import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a file,
so the mandated header comment appears immediately after `import Mathlib`.

## Contents

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. that the only solution of `x ^ p = y ^ q + 1` in integers
`x, y > 1`, `p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`.

This file contains:

* `Frontier.CatalanMihailescu` : the formal statement of the theorem.
* `Frontier.CatalanMihailescuPrimeExponents` : a restricted statement, where the two exponents
  are additionally assumed to be *distinct primes* and the pair of exponents is assumed to be
  different from `(3, 2)`.
* `Frontier.Catalan_Mihailescu` : the **Lean-checked reduction**, namely that the two statements
  above are equivalent. The nontrivial direction uses two unconditionally proved special cases:
  - `Frontier.pow_ne_pow_add_one` : `x ^ n ≠ y ^ n + 1` for `x, y > 1` and `n > 1`
    (equal exponents);
  - `Frontier.cube_ne_sq_add_one` : `x ^ 3 ≠ y ^ 2 + 1` for `y > 0`, i.e. no perfect cube is one
    more than a positive perfect square (the case `(p, q) = (3, 2)`; this is the case `n = 3` of
    a theorem of V. A. Lebesgue). It is proved here by unique factorization in the Gaussian
    integers `ℤ[i]`.
* `Frontier.catalan_base_case` : the base case `3 ^ 2 = 2 ^ 3 + 1`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Units of the Gaussian integers -/

/-- Every unit of `ℤ[i]` has order dividing `4`. -/

theorem pow_ne_pow_add_one (x y n : ℕ) (hy : 1 < y) (hn : 1 < n) :
    x ^ n ≠ y ^ n + 1 := by
  intro h
  have hlt : y ^ n < x ^ n := by omega
  have hxy : y < x := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (by omega : x ≤ y) n) (by omega)
  have h1 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left (by omega) n
  have h2 : y ^ n + 2 ≤ (y + 1) ^ n := succ_pow_ge y hy n hn
  omega

/-! ## The case of the bases `3` and `2` (Levi ben Gerson) -/

/-- **Levi ben Gerson's theorem** (in the form needed here): the only powers of `3` and of `2`
with exponents `> 1` that are consecutive are `9 = 3 ^ 2` and `8 = 2 ^ 3`. -/
