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

noncomputable def maximalMulDomain (m : α → ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (m * (f : α → ℂ)) 2 μ}
  add_mem' := by
    intro f g hf hg
    refine MemLp.ae_eq ?_ (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply, Pi.mul_apply, hx, mul_add]
  zero_mem' := by
    show MemLp (m * ((0 : Lp ℂ 2 μ) : α → ℂ)) 2 μ
    refine MemLp.ae_eq ?_ (MemLp.zero (ε := ℂ) (p := 2) (μ := μ))
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx
    simp only [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c f hf
    refine MemLp.ae_eq ?_ (hf.const_smul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, Pi.mul_apply, hx, smul_eq_mul]
    ring

