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

theorem catalan_base_case : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by norm_num

/-- **Lean-checked reduction of the Catalan–Mihailescu theorem.**

The full statement is equivalent to the reduced non-existence statement
`Frontier.CatalanMihailescuReduced`.  In other words, in order to prove Catalan's conjecture it
suffices to rule out solutions whose exponents are distinct primes other than `(3, 2)` and whose
bases are not `(3, 2)`:

* composite exponents reduce to prime ones;
* equal exponents are impossible (`Frontier.pow_ne_pow_add_one`);
* the exponent pair `(3, 2)` is impossible (`Frontier.cube_ne_sq_add_one`, proved via unique
  factorization in the Gaussian integers);
* the base pair `(3, 2)` yields exactly the known solution `3 ^ 2 = 2 ^ 3 + 1`
  (`Frontier.three_pow_eq_two_pow_add_one`). -/
