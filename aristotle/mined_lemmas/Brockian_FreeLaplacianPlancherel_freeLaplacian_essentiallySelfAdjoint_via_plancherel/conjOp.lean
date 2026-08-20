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

def conjOp (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) :
    conjDomain U D →ₗ[ℂ] H where
  toFun x := U.symm (T ⟨U (x : H), x.2⟩)
  map_add' x y := by
    have : (⟨U ((x + y : conjDomain U D) : H), (x + y).2⟩ : D)
        = ⟨U (x : H), x.2⟩ + ⟨U (y : H), y.2⟩ := by
      ext; simp
    rw [this, map_add, map_add]
  map_smul' c x := by
    have : (⟨U ((c • x : conjDomain U D) : H), (c • x).2⟩ : D)
        = c • ⟨U (x : H), x.2⟩ := by
      ext; simp
    rw [this, map_smul, map_smul]
    rfl

