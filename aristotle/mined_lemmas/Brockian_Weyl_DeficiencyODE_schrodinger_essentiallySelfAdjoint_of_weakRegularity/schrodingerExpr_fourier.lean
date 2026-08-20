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

theorem schrodingerExpr_fourier (n : ℤ) (x : ℝ) :
    -deriv (deriv (fourierFun T n)) x + (V : ℂ) * fourierFun T n x
      = (schrodingerEigenvalue T V n : ℂ) * fourierFun T n x := by
  have hderiv : deriv (fourierFun T n) = fun y => 2 * π * I * n / T * fourierFun T n y := by
    funext y
    exact (hasDerivAt_fourierFun T n y).deriv
  have h2 : deriv (deriv (fourierFun T n)) x
      = (2 * π * I * n / T) * ((2 * π * I * n / T) * fourierFun T n x) := by
    rw [hderiv]
    exact (((hasDerivAt_fourierFun T n x).const_mul (2 * π * I * n / T))).deriv
  rw [h2]
  simp only [schrodingerEigenvalue]
  push_cast
  linear_combination (-(4 * (π : ℂ) ^ 2 * (n : ℂ) ^ 2 / (T : ℂ) ^ 2 * fourierFun T n x)) *
    Complex.I_mul_I

/-- The Schrödinger operator `-d²/dx² + V` on the circle `AddCircle T`, defined on the dense
domain of trigonometric polynomials inside `L²`. -/
