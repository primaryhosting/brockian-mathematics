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
  Brockian/WeylCayley.lean — unitary conjugation of unbounded operators.

  The corpus module of this name was not supplied; this file provides the object
  `conjugatePMap` used by `Brockian.WeylFreeLaplacianCorrected`: the unitary
  conjugate `U T U⁻¹` of a partially defined operator `T`, with domain the image
  `U (dom T)`.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.Cayley

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Unitary conjugation of an unbounded operator.** For a unitary
`e : H ≃ₗᵢ[ℂ] K` and a partially defined operator `T` on `H`, the operator
`e ∘ T ∘ e⁻¹` on `K`, defined on the image `e (dom T)`. -/

theorem fourier_deriv_deriv_schwartz (f : SchwartzMap Real Complex) (xi : Real) :
    𝓕 (deriv (deriv (⇑f))) xi = -(freeSymbol xi) * 𝓕 (⇑f) xi := by
  have hd1 : (⇑(SchwartzMap.derivCLM Complex Complex f) : Real → Complex) = deriv ⇑f :=
    funext fun y => SchwartzMap.derivCLM_apply Complex f y
  set g := SchwartzMap.derivCLM Complex Complex f with hg
  have hd2 : (⇑(SchwartzMap.derivCLM Complex Complex g) : Real → Complex) = deriv ⇑g :=
    funext fun y => SchwartzMap.derivCLM_apply Complex g y
  have h1 : 𝓕 (deriv ⇑f) = fun xi : Real => (2 * Real.pi * Complex.I * xi) • 𝓕 (⇑f) xi :=
    Real.fourier_deriv f.integrable f.differentiable (by rw [← hd1]; exact g.integrable)
  have h2 : 𝓕 (deriv (deriv ⇑f))
      = fun xi : Real => (2 * Real.pi * Complex.I * xi) • 𝓕 (deriv ⇑f) xi := by
    rw [← hd1]
    exact Real.fourier_deriv g.integrable g.differentiable
      (by rw [← hd2]; exact (SchwartzMap.derivCLM Complex Complex g).integrable)
  rw [h2, h1, freeSymbol]
  push_cast
  simp only [smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The Fourier transform turns `-d²/dx²` on the Schwartz core into
multiplication by the free symbol. -/
