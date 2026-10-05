import Mathlib

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The standard recursion generating solutions of `x² - 3y² = 1` from the
fundamental solution `(2, 1)`: `(x, y) ↦ (2x + 3y, x + 2y)`. -/

lemma pellSol_strictMono : StrictMono fun n => (pellSol n).2 :=
  strictMono_nat_of_lt_succ pellSol_lt_succ

/-- **Pell's equation for `d = 3`.** The equation `x² - 3y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0`. -/
