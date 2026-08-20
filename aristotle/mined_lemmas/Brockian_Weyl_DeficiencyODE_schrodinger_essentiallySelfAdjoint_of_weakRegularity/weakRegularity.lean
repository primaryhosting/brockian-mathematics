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

theorem weakRegularity (z : ℂ) (u : Lp ℂ 2 (@haarAddCircle T hT))
    (hu : IsDeficiencyVector (schrodingerOp T V) z u) (n : ℤ) :
    ((schrodingerEigenvalue T V n : ℂ) - conj z) * fourierCoeff u n = 0 := by
  have h := hu (spanBasis fourierBasis n)
  rw [schrodingerOp, diagOp_basis, spanBasis_apply, ← sub_smul, inner_smul_left] at h
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simpa [map_sub] using h

/-- **The Schrödinger operator `-d²/dx² + V` with constant potential `V` on the circle is
essentially self-adjoint on trigonometric polynomials.**  Formerly conditional on a weak-regularity
hypothesis for the deficiency ODE; that hypothesis is discharged by `weakRegularity`. -/
