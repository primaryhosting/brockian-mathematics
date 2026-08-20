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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

def mulDomain : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | mulSymbol m hm μ * (f : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ}
  add_mem' := by
    intro a b ha hb
    have h : mulSymbol m hm μ * ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
        = mulSymbol m hm μ * (a : X →ₘ[μ] ℂ) + mulSymbol m hm μ * (b : X →ₘ[μ] ℂ) := by
      rw [show ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = (a : X →ₘ[μ] ℂ) + (b : X →ₘ[μ] ℂ) from rfl,
        aeeqfun_mul_add]
    show mulSymbol m hm μ * ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [h]
    exact add_mem ha hb
  zero_mem' := by
    show mulSymbol m hm μ * ((0 : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [show ((0 : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = 0 from rfl, aeeqfun_mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha
    have h : mulSymbol m hm μ * ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
        = c • (mulSymbol m hm μ * (a : X →ₘ[μ] ℂ)) := by
      rw [show ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = c • (a : X →ₘ[μ] ℂ) from rfl,
        aeeqfun_mul_smul]
    show mulSymbol m hm μ * ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [h]
    exact (c • (⟨_, ha⟩ : Lp ℂ 2 μ)).2

/-- The maximal multiplication operator by the real measurable function `m` on `L²(μ)`. -/
