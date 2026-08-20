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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1) = (10 ^ n - 1) / 9`,
i.e. the number written with `n` ones in base ten. -/

lemma repunit_eq_one_iff {n : ℕ} : repunit n = 1 ↔ n = 1 := by
  constructor
  · intro h
    exact repunit_injective (by simpa using h)
  · rintro rfl; rfl

/-- Multiplicative structure: `R (d * k) = R d * ∑_{i < k} (10 ^ d) ^ i`. -/
