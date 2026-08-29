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

theorem freeSchrodingerPMap_le_spectralFreeLaplacian :
    freeSchrodingerPMap ≤ spectralFreeLaplacian := by
  constructor
  · intro u hu
    obtain ⟨f, rfl⟩ := (LinearMap.mem_range).mp hu
    exact schwartzToL2_mem_spectralFreeLaplacian_domain f
  · intro x y hxy
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
    have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
    have hyc : (y : L2R) = schwartzToL2 f := by rw [← hxy, ← hf]
    rw [hxe, freeSchrodingerPMap_toFun_ofInjective, freeCoreMap_apply,
      spectralFreeLaplacian_schwartz f y hyc]

end Brockian.Weyl.FreeLaplacianCorrected

/-
  Brockian/WeylSchrodingerMinimal.lean — the Schwartz core embedded in `L²(ℝ)`,
  the second-derivative operator on that core, and Schwartz integration by parts.

  This file reproduces, verbatim, the part of the supplied corpus module
  `Brockian.WeylSchrodingerMinimal` whose dependencies are Mathlib only, namely
  everything up to and including `kinetic_symm`:

    `H2`, `schwartzToL2`, `schwartzToL2_apply`, `coeFn_schwartzToL2`,
    `schwartzToL2_injective`, `D2`, `D2_apply`, `Lconj`, `Lconj_apply`,
    `schwartz_ibp1`, `schwartz_ibp2`, `inner_toLp`, `kinetic_symm`.

  The remaining declarations of that corpus module (the bounded potential term
  `potentialMulCLM`, `coreMap`, `schrodingerPMap` and their consequences) are
  phrased in terms of `mulLpCLM` / `isSelfAdjoint_mulLpCLM` / the
  `DeficiencyRepresentsODE` bridge, which live in corpus modules
  (`Brockian.SpectralGate1`, `Brockian.WeylBridge`,
  `Brockian.WeylSchrodingerESA`) that were not supplied here; they are therefore
  not reproduced. None of them is used downstream in this development.
-/
import Mathlib
import Brockian.WeylOperator

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-! ### The Schwartz core embedded in L² -/

/-- **The Schwartz core, embedded in `L²`.** The ℂ-linear map sending a Schwartz
function to its `L²` class. Its range is the (dense) domain of the minimal
operator. -/
