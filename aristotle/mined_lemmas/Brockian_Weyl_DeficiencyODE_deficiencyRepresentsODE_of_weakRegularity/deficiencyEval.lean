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
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- The state space of a first-order linear system of `n` equations. -/
abbrev State (n : ℕ) : Type := Fin n → ℂ

variable {n : ℕ}

/-- *Weak regularity* of the coefficient family of the first-order linear system
`u' t = A t (u t)`: the coefficient operators depend continuously on time.  This is the
hypothesis retained in the Weyl-theoretic statement below. -/

def deficiencyEval (A : ℝ → (State n →L[ℂ] State n)) :
    deficiencySpace A →ₗ[ℂ] State n where
  toFun u := (u : ℝ → State n) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Uniqueness for the linear system: a solution vanishing at one time vanishes
identically. -/
