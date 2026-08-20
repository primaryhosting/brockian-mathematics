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

theorem andrica_zero : Real.sqrt (prime 1) - Real.sqrt (prime 0) < 1 := by
  refine andrica_of_gap_le_two 0 ?_
  have h0 : prime 0 = 2 := prime_zero
  have h1 : prime (0 + 1) = 3 := by
    have hc : Nat.count Nat.Prime 3 = 1 := by decide
    have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
    rw [hc] at h
    simp [prime, h]
  omega

end Brockian.AndricaConjecture

