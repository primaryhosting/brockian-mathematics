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

theorem coeFn_maximalMul (m : α → ℂ) (f : (maximalMul (μ := μ) m).domain) :
    ((maximalMul m f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] m * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  MemLp.coeFn_toLp f.2

end Brockian.Weyl.MaximalMultiplication

/-
  Brockian/WeylFreeLaplacianCorrected.lean — the correctly normalised spectral
  free Laplacian `F⁻¹ M_{4π²ξ²} F` on `L²(ℝ)`, and the restriction of the
  Schwartz-core free Schrödinger operator into it.

  The declarations up to `spectralFreeLaplacian` are the supplied corpus source.
  The declarations of the corpus module that are phrased in terms of the Cayley
  criterion (`rangeSMulSub`, `essentiallySelfAdjoint_iff`,
  `conjugatePMap_essentiallySelfAdjoint`, and the two essential
  self-adjointness theorems they prove) live in corpus modules that were not
  supplied, and are not reproduced here; nothing below depends on them.
-/
import Brockian.WeylMaximalMultiplication
import Brockian.WeylSchrodingerGate1Final
import Brockian.WeylCayley
import Brockian.FreeLaplacianPlancherel

open MeasureTheory
open scoped InnerProductSpace FourierTransform ENNReal

namespace Brockian.Weyl.FreeLaplacianCorrected

open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The physical Fourier symbol for `-d^2/dx^2` under Mathlib's
`exp(-2*pi*i*x*xi)` convention. -/
