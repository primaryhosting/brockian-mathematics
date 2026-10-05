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

theorem kinetic_symm (f g : SchwartzMap ℝ ℂ) :
    ⟪schwartzToL2 (D2 f), schwartzToL2 g⟫_ℂ = ⟪schwartzToL2 f, schwartzToL2 (D2 g)⟫_ℂ := by
  rw [inner_toLp, inner_toLp]
  simp only [D2_apply]
  exact schwartz_ibp2 f g

end Brockian.Weyl.SchrodingerMinimal

/-
  Brockian/FreeLaplacianPlancherel.lean — the Plancherel unitary on `L²(ℝ)`.

  The corpus module of this name was not supplied; this file provides the object
  `Brockian.FreeLaplacianPlancherel.fourierL2` used by
  `Brockian.WeylFreeLaplacianCorrected`: the Fourier transform as a unitary of
  `L²(ℝ)`, taken from Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`, together
  with the two facts that it agrees with the Schwartz Fourier transform on the
  Schwartz core.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal

open MeasureTheory SchwartzMap
open scoped FourierTransform

namespace Brockian.FreeLaplacianPlancherel

open Brockian.Weyl.SchrodingerMinimal

/-- **The Plancherel unitary** `𝓕 : L²(ℝ) ≃ₗᵢ[ℂ] L²(ℝ)`. -/
