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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wilson Prime Infinitude

Category: Brockian Conjecture.  Target: `Brockian.WilsonPrimes.WilsonPrimeInfinitude`.

Note: the header block above is kept as an ordinary comment because Lean requires `import`
commands to precede every other command, including module docstrings.
-/

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`.
(By Wilson's theorem every prime satisfies `p ∣ (p - 1)! + 1`; a Wilson prime is one for
which the stronger congruence modulo `p ^ 2` holds.) -/

theorem isWilsonPrime_lt_1000_iff (p : ℕ) (hp : p < 1000) :
    IsWilsonPrime p ↔ (p = 5 ∨ p = 13 ∨ p = 563) := by
  have key : ∀ q < 1000, (q.Prime ∧ q ^ 2 ∣ (q - 1)! + 1) ↔ (q = 5 ∨ q = 13 ∨ q = 563) := by
    decide
  exact key p hp

/-- There exists at least one Wilson prime. -/
