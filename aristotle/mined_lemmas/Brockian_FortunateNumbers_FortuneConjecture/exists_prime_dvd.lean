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

theorem exists_prime_dvd : ∀ m : Nat, 2 ≤ m → ∃ p, IsPrime p ∧ p ∣ m := by
  intro m hm
  by_cases hp : IsPrime m
  · exact ⟨m, hp, Nat.dvd_refl m⟩
  · obtain ⟨p, hp, hpd, _⟩ := exists_prime_factor_sq_le m hm hp
    exact ⟨p, hp, hpd⟩

/-! ## Infinitude of primes -/

/-- The factorial function. -/
