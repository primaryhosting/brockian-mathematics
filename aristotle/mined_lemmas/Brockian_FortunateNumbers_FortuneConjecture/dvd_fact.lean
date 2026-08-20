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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem dvd_fact : ∀ {k n : Nat}, 1 ≤ k → k ≤ n → k ∣ fact n
  | k, 0, hk, hkn => absurd hkn (by omega)
  | k, n + 1, hk, hkn => by
      rw [fact]
      by_cases h : k = n + 1
      · exact ⟨fact n, by rw [h]⟩
      · exact Nat.dvd_trans (dvd_fact hk (by omega)) (Nat.dvd_mul_left (fact n) (n + 1))

/-- Euclid: there are arbitrarily large primes. -/
