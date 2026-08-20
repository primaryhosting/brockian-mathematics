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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Lean requires `import` commands to precede every other command, including module
docstrings, so the mandated header appears at the top of the file as a plain block
comment and is repeated here as the module docstring.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/

lemma sqrt_sub_sqrt_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt b - Real.sqrt a < 1 ↔ b - a < 2 * Real.sqrt a + 1 := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hpos : (0:ℝ) < 1 + Real.sqrt a := by linarith
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  constructor
  · intro h
    have h1 : Real.sqrt b < 1 + Real.sqrt a := by linarith
    have hb : b < (1 + Real.sqrt a) ^ 2 := (Real.sqrt_lt' hpos).mp h1
    nlinarith [hsq]
  · intro h
    have hb : b < (1 + Real.sqrt a) ^ 2 := by nlinarith [hsq]
    have := (Real.sqrt_lt' hpos).mpr hb
    linarith

/-- The two formulations of the Andrica conjecture are equivalent. -/
