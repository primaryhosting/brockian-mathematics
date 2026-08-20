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

lemma conjOp_essentiallySelfAdjoint (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (h : IsEssentiallySelfAdjoint D T) :
    IsEssentiallySelfAdjoint (conjDomain U D) (conjOp U T) := by
  obtain ⟨hdense, hsymm, hplus, hminus⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have himg : ((conjDomain U D : Submodule ℂ H) : Set H) = U.symm '' (D : Set H) := by
      ext w
      constructor
      · intro hw
        exact ⟨U w, hw, by simp⟩
      · rintro ⟨v, hv, rfl⟩
        show U (U.symm v) ∈ D
        simpa using hv
    rw [himg]
    exact U.symm.surjective.denseRange.dense_image U.symm.continuous hdense
  · intro x y
    rw [conjOp_apply, conjOp_apply, inner_symm_left, inner_symm_right]
    exact hsymm ⟨U (x : H), x.2⟩ ⟨U (y : H), y.2⟩
  · exact conjOp_dense_range U T Complex.I hplus
  · have hminus' : Dense (Set.range fun x : D => T x + (-Complex.I) • (x : H)) := by
      simpa [sub_eq_add_neg] using hminus
    have := conjOp_dense_range U T (-Complex.I) hminus'
    simpa [sub_eq_add_neg] using this

end Conjugation

/-! ## The maximal multiplication operator by a real measurable function -/
section Multiplication

variable {X : Type*} [MeasurableSpace X]

section Aux

variable {μ : Measure X}

