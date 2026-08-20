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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- Primality of a natural number, stated from first principles (this file is self-contained
and imports nothing beyond Lean's prelude, so that the header comment above can literally be
the first thing in the file). -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

instance : DecidablePred IsPrimeNat := fun p => by
  unfold IsPrimeNat
  exact decidable_of_iff (2 ≤ p ∧ ∀ d < p + 1, d ∣ p → d = 1 ∨ d = p)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun d hd => h2 d (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)) hd⟩,
     fun ⟨h1, h2⟩ => ⟨h1, fun d _ hd => h2 d hd⟩⟩

/-- **Oppermann's conjecture** (statement form): for every `n ≥ 2` there is a prime strictly
between `n * (n - 1)` and `n * n`, and a prime strictly between `n * n` and `n * (n + 1)`. -/
