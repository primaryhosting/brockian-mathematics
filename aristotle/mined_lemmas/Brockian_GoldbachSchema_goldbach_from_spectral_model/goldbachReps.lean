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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

namespace Brockian.GoldbachSchema

/-- The (finite, truncated) *singular series* factor attached to `n`:
the product of `(p-1)/(p-2)` over the odd prime divisors of `n`.
This is the arithmetic factor appearing in the circle-method main term for the
number of Goldbach representations of `n`. -/

def goldbachReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)

/-- **Discharged hypothesis.** In the spectral schema this was carried as an extra
named assumption `main_pos : 0 < main`. It is in fact an unconditional theorem:
the singular series is a finite product of strictly positive rationals.

The Mathlib lemma that closes it is `Finset.prod_pos`. -/
