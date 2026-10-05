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

theorem fourier_neg_D2_eq (f : SchwartzMap Real Complex) :
    𝓕 (-(D2 f)) = freeSymbolMulSchwartz (𝓕 f) := by
  have hneg : 𝓕 (-(D2 f)) = -(𝓕 (D2 f)) := by
    rw [← SchwartzMap.fourierTransformCLM_apply Complex,
      ← SchwartzMap.fourierTransformCLM_apply Complex, map_neg]
  have hD2 : (⇑(D2 f) : Real → Complex) = deriv (deriv ⇑f) := funext fun x => D2_apply f x
  ext xi
  rw [hneg, freeSymbolMulSchwartz_apply, SchwartzMap.neg_apply,
    SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hD2, fourier_deriv_deriv_schwartz]
  ring

/-- The inverse Fourier transform of `freeSymbol · 𝓕 f` is `-f″`. -/
