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

theorem freeSchrodingerPMap_isSymmetric : IsSymmetric freeSchrodingerPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, freeSchrodingerPMap_toFun_ofInjective, freeSchrodingerPMap_toFun_ofInjective,
    LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, freeCoreMap_apply,
    freeCoreMap_apply, inner_neg_left, inner_neg_right, kinetic_symm f g]

end Brockian.Weyl.SchrodingerGate1Final

/-
  Brockian/WeylMaximalMultiplication.lean — maximal multiplication operators on
  `L²`.

  The corpus module of this name was not supplied; this file provides the object
  `maximalMul` used by `Brockian.WeylFreeLaplacianCorrected`, defined in the
  standard way: the multiplication operator `f ↦ m · f` with its *maximal*
  domain `{f ∈ L² | m · f ∈ L²}`.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal

open MeasureTheory

namespace Brockian.Weyl.MaximalMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The maximal domain of multiplication by `m` inside `L²(μ)`: the set of `L²`
classes `f` such that `m · f` is again square integrable. -/
