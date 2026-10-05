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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header is repeated verbatim as a module docstring just below the import.)

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so we do not prove it
outright.  Instead we give a Lean-checked *equivalent reformulation*: the set of
exponents `p` for which `2 ^ p - 1` is prime is infinite **if and only if** the set of
even perfect numbers is infinite.  The equivalence comes from the Euclid–Euler
theorem, which is reproved here (following the Mathlib archive development of the
Euclid–Euler theorem) so that the file depends only on `Mathlib` itself.

We also record the contrapositive form: there are only finitely many Mersenne primes
iff there are only finitely many even perfect numbers.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-! ### The Euclid–Euler theorem -/


theorem euclidEuler_lt_euclidEuler {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    euclidEuler p < euclidEuler q := by
  have h1 : (2 : ℕ) ^ (p - 1) ≤ 2 ^ (q - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne p < mersenne q := by
    have hlt : (2 : ℕ) ^ p < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) hpq
    have h2p : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have hmp : 0 < mersenne p := by
    have h2p : (2 : ℕ) ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    simp only [mersenne]
    omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 (by positivity)

/-- The Euclid–Euler map is injective on the set of Mersenne exponents. -/
