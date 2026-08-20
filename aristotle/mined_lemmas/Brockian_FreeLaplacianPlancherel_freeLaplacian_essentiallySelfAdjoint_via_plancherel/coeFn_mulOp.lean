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

lemma coeFn_mulOp (f : mulDomain m hm μ) :
    ⇑(mulOp m hm μ f) =ᵐ[μ] fun x => (m x : ℂ) * (f : Lp ℂ 2 μ) x := by
  have h1 : ⇑(mulOp m hm μ f)
      = ((mulSymbol m hm μ * ((f : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) : X →ₘ[μ] ℂ) : X → ℂ) := rfl
  rw [h1]
  filter_upwards [AEEqFun.coeFn_mul (mulSymbol m hm μ) ((f : Lp ℂ 2 μ) : X →ₘ[μ] ℂ),
    coeFn_mulSymbol m hm μ] with x hx hs
  rw [hx]
  simp [hs]

/-- Given a bounded measurable multiplier `u` such that `m * u` is also bounded, and any
`z ∈ L²`, the product `u * z` lies in the domain of the multiplication operator. -/
