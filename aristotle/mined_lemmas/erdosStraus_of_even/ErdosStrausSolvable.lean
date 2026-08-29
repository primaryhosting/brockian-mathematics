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

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/

def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 : ℚ) / (n : ℚ) = 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ)

/-- The Erdős–Straus conjecture (**OPEN**), recorded as an unproven
`def`: every `n ≥ 2` admits such a representation. -/
