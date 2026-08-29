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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`, `prime 1 = 3`, ...). -/

theorem five_le_prime {n : ℕ} (hn : 2 ≤ n) : 5 ≤ prime n := by
  have := prime_strictMono.monotone hn
  rwa [prime_two] at this

/-! ## The reformulation of Andrica's inequality -/

/-- Andrica's inequality `√y - √x < 1` is equivalent to the "gap" inequality
`y < x + 2√x + 1`. This is the standard reformulation of the conjecture. -/
