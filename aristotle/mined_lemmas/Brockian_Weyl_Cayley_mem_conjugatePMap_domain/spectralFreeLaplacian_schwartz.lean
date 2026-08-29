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

theorem spectralFreeLaplacian_schwartz (f : SchwartzMap Real Complex)
    (y : spectralFreeLaplacian.domain) (hy : (y : L2R) = schwartzToL2 f) :
    spectralFreeLaplacian y = -(schwartzToL2 (D2 f)) := by
  have hmem : schwartzToL2 (𝓕 f) ∈ freeSymbolMaximal.domain :=
    schwartzToL2_mem_freeSymbolMaximal_domain _
  have hval : spectralFreeLaplacian y
      = Brockian.FreeLaplacianPlancherel.fourierL2.symm
          (freeSymbolMaximal ⟨schwartzToL2 (𝓕 f), hmem⟩) := by
    refine conjugatePMap_apply _ freeSymbolMaximal ⟨schwartzToL2 (𝓕 f), hmem⟩ y ?_
    rw [hy]
    show schwartzToL2 f
      = Brockian.FreeLaplacianPlancherel.fourierL2.symm (schwartzToL2 (𝓕 f))
    rw [← Brockian.FreeLaplacianPlancherel.fourierL2_schwartzToL2,
      LinearIsometryEquiv.symm_apply_apply]
  rw [hval, freeSymbolMaximal_schwartz (𝓕 f) _ rfl,
    Brockian.FreeLaplacianPlancherel.fourierL2_symm_schwartzToL2,
    fourierInv_freeSymbolMul_eq f, map_neg]

