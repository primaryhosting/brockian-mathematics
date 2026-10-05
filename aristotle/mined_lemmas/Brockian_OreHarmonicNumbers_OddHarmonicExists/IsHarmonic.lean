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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The number of divisors of `n`, usually written `τ (n)` or `d (n)`. -/

def IsHarmonic (n : ℕ) : Prop := 0 < n ∧ sigma n ∣ n * tau n

instance (n : ℕ) : Decidable (IsHarmonic n) := by
  unfold IsHarmonic; infer_instance

/-- The harmonic mean of the divisors of `n`, as a rational number. -/
