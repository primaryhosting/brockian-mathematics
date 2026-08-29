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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/

lemma one_lt_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : 1 < n := by
  rcases h with ⟨hpos, heq⟩
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · simp [usigma_one] at heq
  · omega

/-- If `n` is unitary perfect, then its number of odd prime factors is at most
`v₂(n) + 1`, where `v₂` denotes the 2-adic valuation. -/
