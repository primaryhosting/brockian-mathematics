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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real ComplexConjugate InnerProductSpace
open Complex MeasureTheory Submodule AddCircle Module

namespace Brockian.Weyl.DeficiencyODE

/-! ## Abstract setting: symmetric operators, deficiency vectors, essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

/-- A densely defined operator `T` with domain `D` is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

def IsDeficiencyVector (T : D →ₗ[ℂ] H) (z : ℂ) (u : H) : Prop :=
  ∀ x : D, ⟪T x - z • (x : H), u⟫_ℂ = 0

/-- Essential self-adjointness in the form of von Neumann's basic criterion: the operator is
densely defined, symmetric, and both deficiency spaces (at `z = i` and at `z = -i`) are trivial. -/
structure EssentiallySelfAdjoint (T : D →ₗ[ℂ] H) : Prop where
  dense_domain : Dense (D : Set H)
  symmetric : IsSymmetric T
  deficiency_pos : ∀ u : H, IsDeficiencyVector T Complex.I u → u = 0
  deficiency_neg : ∀ u : H, IsDeficiencyVector T (-Complex.I) u → u = 0

variable {ι : Type*}

/-- The algebraic basis of the algebraic span of a Hilbert basis. -/
