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

import Mathlib

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## The Euclid–Euler theorem

The proofs in this section follow the classical Euclid–Euler argument (as formalized in
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` in mathlib, which is not available as an
import here). -/


theorem le_euclid_number (k : ℕ) : k + 1 ≤ 2 ^ k * mersenne (k + 1) := by
  have h1 : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have h2 : 1 ≤ mersenne (k + 1) := by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [mersenne]
    omega
  calc k + 1 ≤ 2 ^ k := h1
    _ = 2 ^ k * 1 := (mul_one _).symm
    _ ≤ 2 ^ k * mersenne (k + 1) := Nat.mul_le_mul_left _ h2

/-! ## Main result -/

/-- **Even Perfect Infinitude.**  There are infinitely many even perfect numbers if and only if
there are infinitely many Mersenne primes.  (Whether either side actually holds is a famous open
problem; this theorem is the unconditional reduction of one to the other, and is proved via the
Euclid–Euler theorem.) -/
