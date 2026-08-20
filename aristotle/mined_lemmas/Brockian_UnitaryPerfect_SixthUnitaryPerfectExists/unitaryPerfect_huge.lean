import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem unitaryPerfect_huge : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have e : (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 ^ 1 * (5 ^ 4 * (7 ^ 1 * (11 ^ 1 * (13 ^ 1 * (19 ^ 1 * (37 ^ 1 *
        (79 ^ 1 * (109 ^ 1 * (157 ^ 1 * 313 ^ 1)))))))))) := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 313) (k := 1) (by norm_num) (by norm_num)]
  norm_num

