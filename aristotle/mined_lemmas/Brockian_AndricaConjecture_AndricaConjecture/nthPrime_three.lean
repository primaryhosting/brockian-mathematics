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

namespace Brockian.AndricaConjecture

open Real

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`). -/

lemma nthPrime_three : nthPrime 3 = 7 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 7) = 7 := Nat.nth_count (by norm_num)
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rw [hc] at h
  exact h

/-- Unconditional verification of the Andrica inequality at `n = 0`: `√3 - √2 < 1`. -/
