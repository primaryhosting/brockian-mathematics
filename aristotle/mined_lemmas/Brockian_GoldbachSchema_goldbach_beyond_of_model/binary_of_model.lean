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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian
namespace GoldbachSchema

/-- The binary Goldbach property: `n` is a sum of two primes. -/

theorem binary_of_model (M : Model) {n : ℕ} (hn : M.bound ≤ n) (hev : Even n) :
    Goldbach2 n := by
  refine ⟨M.witness n, n - M.witness n, M.witness_prime n hn hev,
    M.cowitness_prime n hn hev, ?_⟩
  have := M.witness_le n hn hev
  omega

/-- Conversely, binary Goldbach beyond a bound `B` yields a model with that bound: the notion of
`Model` is exactly a packaging of the binary Goldbach property beyond a bound. -/
