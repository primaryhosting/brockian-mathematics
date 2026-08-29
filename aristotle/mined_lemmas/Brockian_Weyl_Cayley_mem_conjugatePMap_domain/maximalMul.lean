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

noncomputable def maximalMul (m : α → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain m
  toFun :=
    { toFun := fun f => MemLp.toLp _ f.2
      map_add' := by
        intro f g
        refine Lp.ext ?_
        filter_upwards [(MemLp.coeFn_toLp (f + g).2), Lp.coeFn_add (MemLp.toLp _ f.2)
          (MemLp.toLp _ g.2), MemLp.coeFn_toLp f.2, MemLp.coeFn_toLp g.2,
          Lp.coeFn_add (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)] with x h1 h2 h3 h4 h5
        rw [h1, h2]
        simp only [Pi.add_apply]
        rw [h3, h4]
        have hfg : ((f + g : maximalMulDomain m) : Lp ℂ 2 μ) = (f : Lp ℂ 2 μ) + g := rfl
        rw [hfg]
        simp only [Pi.mul_apply, Pi.add_apply, h5, mul_add]
      map_smul' := by
        intro c f
        refine Lp.ext ?_
        filter_upwards [(MemLp.coeFn_toLp (c • f).2), Lp.coeFn_smul c (MemLp.toLp _ f.2),
          MemLp.coeFn_toLp f.2, Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2]
        simp only [Pi.smul_apply]
        rw [h3]
        have hcf : ((c • f : maximalMulDomain m) : Lp ℂ 2 μ) = c • (f : Lp ℂ 2 μ) := rfl
        rw [hcf]
        simp only [Pi.mul_apply, Pi.smul_apply, h4, smul_eq_mul]
        ring }

