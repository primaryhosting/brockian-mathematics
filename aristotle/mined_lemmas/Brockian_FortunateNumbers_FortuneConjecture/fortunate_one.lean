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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- The `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem fortunate_one : fortunate 1 = 5 := by
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [primorialOf_one]; norm_num⟩, ?_⟩
  intro m hm hmem
  rw [primorialOf_one] at hmem
  interval_cases m
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.2 (by norm_num)
  · exact absurd hmem.2 (by norm_num)
  · exact absurd hmem.2 (by norm_num)

end Brockian.FortunateNumbers

