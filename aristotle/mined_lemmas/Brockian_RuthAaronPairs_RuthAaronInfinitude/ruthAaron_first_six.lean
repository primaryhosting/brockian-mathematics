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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(A001414, the "integer logarithm"). By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem ruthAaron_first_six :
    ({5, 8, 15, 77, 125, 714} : Set ℕ) ⊆ {n : ℕ | IsRuthAaronPair n} := by
  rintro n (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact isRuthAaronPair_five
  · exact isRuthAaronPair_eight
  · exact isRuthAaronPair_fifteen
  · exact isRuthAaronPair_seventyseven
  · exact isRuthAaronPair_125
  · exact isRuthAaronPair_714

/-- There are at least six Ruth–Aaron pairs. -/
