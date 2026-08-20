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

def mulOp : mulDomain m hm μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ⟨mulSymbol m hm μ * (f : X →ₘ[μ] ℂ), f.2⟩
  map_add' f g := by
    apply Subtype.ext
    show mulSymbol m hm μ * ((f : X →ₘ[μ] ℂ) + (g : X →ₘ[μ] ℂ))
        = mulSymbol m hm μ * (f : X →ₘ[μ] ℂ) + mulSymbol m hm μ * (g : X →ₘ[μ] ℂ)
    rw [aeeqfun_mul_add]
  map_smul' c f := by
    apply Subtype.ext
    show mulSymbol m hm μ * (c • (f : X →ₘ[μ] ℂ)) = c • (mulSymbol m hm μ * (f : X →ₘ[μ] ℂ))
    rw [aeeqfun_mul_smul]

