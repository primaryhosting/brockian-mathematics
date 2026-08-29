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

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/

theorem goldbach_model_2002 : GoldbachModel 2002 :=
  model_of_gCheck (k := 44) (M := 1000) (by decide +kernel)

/-! ## The target: the model hypothesis discharged -/

/-- **Goldbach beyond, with the model hypothesis discharged.**

Every odd number `n` with `9 ≤ n ≤ 2005` is a sum of three primes.

This is the conclusion of the schema `ternary_of_model`, whose `GoldbachModel` hypothesis has
been discharged unconditionally (by the kernel-checked computation `goldbach_model_2002`), so
the statement below carries no hypotheses beyond the arithmetic constraints on `n`.
The corresponding statement for all odd `n ≥ 9` would follow from the schema applied to an
unbounded model, i.e. from Goldbach's conjecture, which remains open. -/
