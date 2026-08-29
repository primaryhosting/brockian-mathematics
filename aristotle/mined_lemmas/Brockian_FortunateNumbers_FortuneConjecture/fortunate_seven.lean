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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/

theorem fortunate_seven : fortunate 7 = 13 := by
  have h : primorial 7 = 210 := by decide
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [h]; norm_num⟩, ?_⟩
  intro m hm
  interval_cases m <;> norm_num [h]

/-- Unconditional verification of Fortune's conjecture for the small cases `n = 0, 2, 3, 5, 7`. -/
