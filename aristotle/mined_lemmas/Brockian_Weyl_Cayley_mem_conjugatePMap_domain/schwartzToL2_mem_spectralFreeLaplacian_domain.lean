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

theorem schwartzToL2_mem_spectralFreeLaplacian_domain (f : SchwartzMap Real Complex) :
    schwartzToL2 f ∈ spectralFreeLaplacian.domain := by
  refine ⟨Brockian.FreeLaplacianPlancherel.fourierL2 (schwartzToL2 f), ?_, ?_⟩
  · rw [Brockian.FreeLaplacianPlancherel.fourierL2_schwartzToL2]
    exact schwartzToL2_mem_freeSymbolMaximal_domain _
  · exact (Brockian.FreeLaplacianPlancherel.fourierL2).symm_apply_apply _

/-- The spectral free Laplacian acts on the Schwartz core as `-d²/dx²`. -/
