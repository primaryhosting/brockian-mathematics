/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number: `n` is at least `2` and its only divisors are `1` and `n`.

This file is required to begin with the header comment above, which Lean parses as a module
documentation command; consequently no `import` line may follow it, so the development below is
carried out with the Lean core library only, and primality is spelled out explicitly here
(this predicate is equivalent to Mathlib's `Nat.Prime`). -/

theorem quadruplet_11_13_17_19_natPrime :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 :=
  ⟨(isPrime_iff_nat_prime 11).mp isPrime_eleven,
   (isPrime_iff_nat_prime 13).mp isPrime_thirteen,
   (isPrime_iff_nat_prime 17).mp isPrime_seventeen,
   (isPrime_iff_nat_prime 19).mp isPrime_nineteen, rfl, rfl, rfl⟩

end Constellation

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

