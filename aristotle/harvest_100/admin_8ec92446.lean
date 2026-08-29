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
# Dirichlet Sum Eq Zero
Category: Characters
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Characters5

/-- Orthogonality for a nontrivial Dirichlet character mod 5 with values in `ℂ`:
the sum of its values over `ZMod 5` vanishes.

This is `MulChar.sum_eq_zero_of_ne_one` (Mathlib.NumberTheory.MulChar.Basic),
since `DirichletCharacter ℂ 5` unfolds to `MulChar (ZMod 5) ℂ` and `ℂ` is a domain. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Brockian.Characters5

