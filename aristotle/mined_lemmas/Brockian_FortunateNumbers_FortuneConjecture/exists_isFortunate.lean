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

theorem exists_isFortunate (n : Nat) : ∃ m, IsFortunate n m := by
  obtain ⟨p, hp, hpgt⟩ := exists_prime_gt (primorial n + 1)
  have hex : ∃ m, 1 < m ∧ IsPrime (primorial n + m) := by
    refine ⟨p - primorial n, by omega, ?_⟩
    have : primorial n + (p - primorial n) = p := by omega
    rw [this]; exact hp
  obtain ⟨m, ⟨hm1, hmp⟩, hmin⟩ := exists_least _ hex
  exact ⟨m, hm1, hmp, fun k hk hk1 hkp => hmin k hk ⟨hk1, hkp⟩⟩

/-- The fortunate number of a given index is unique. -/
