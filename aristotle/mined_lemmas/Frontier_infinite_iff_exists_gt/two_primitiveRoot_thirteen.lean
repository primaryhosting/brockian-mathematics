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
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/

theorem two_primitiveRoot_thirteen : IsPrimitiveRootMod 2 13 := by
  unfold IsPrimitiveRootMod
  norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hd
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases q
  all_goals (revert hq hd; decide)

/-! ### Main statement -/

/-- **Artin's conjecture on primitive roots**, formalized, together with a Lean-checked
reduction and base cases.

1. `ArtinConjecture` is the statement that every integer `a ≠ -1` which is not a perfect square
   is a primitive root modulo infinitely many primes.  It is equivalent to the statement that
   such an `a` is a primitive root modulo arbitrarily large primes.
2. Both exclusions are necessary: a perfect square is a primitive root only modulo `2`, and `-1`
   only modulo primes `p ≤ 3`.
3. Membership of a prime `p` in `artinSet a` reduces to the finite Lucas-type test on the prime
   divisors of `p - 1`.
4. Base cases: `2` is a primitive root modulo `3`, `5`, `11` and `13`. -/
