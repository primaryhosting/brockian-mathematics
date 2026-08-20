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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


noncomputable def relEntropy (ρ σ : Mat n) : ℝ :=
  (ρ * logM ρ).trace.re - (ρ * logM σ).trace.re

/-- A matrix is a density matrix (a *faithful* quantum state) when it is positive definite of
unit trace. -/
structure IsState (ρ : Mat n) : Prop where
  posDef : ρ.PosDef
  trace_eq_one : ρ.trace = 1

/-- A family `E : Y → Mat n` is a POVM (positive operator valued measure) when all its elements
are positive semidefinite and they sum to the identity. -/
structure IsPOVM {Y : Type*} [Fintype Y] (E : Y → Mat n) : Prop where
  posSemidef : ∀ y, (E y).PosSemidef
  sum_eq_one : ∑ y, E y = 1

/-- The Shannon mutual information of a joint probability distribution `P` on `X × Y`. -/
