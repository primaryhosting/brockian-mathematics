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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/

theorem solvable_of_lt_1000 {n : ℕ} (hn : 2 ≤ n) (h : n < 1000) : Solvable n := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hple : p ≤ n := Nat.le_of_dvd (by omega) hpd
  by_cases hm : p % 24 = 1
  · exact Solvable.of_dvd (by omega) hpd
      (solvable_of_prime_one_mod_24_lt_1000 hp hm (by omega))
  · exact Solvable.of_dvd (by omega) hpd (solvable_of_mod_24_ne_one hp.two_le hm)

end SmallPrimes

/-- **Conditional reduction.** The Erdős–Straus conjecture follows from its special case
for primes `p ≡ 1 [MOD 24]`. -/
