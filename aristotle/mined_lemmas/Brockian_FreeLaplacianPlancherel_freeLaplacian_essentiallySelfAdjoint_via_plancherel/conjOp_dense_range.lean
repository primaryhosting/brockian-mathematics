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

lemma conjOp_dense_range (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (c : ℂ)
    (hd : Dense (Set.range fun x : D => T x + c • (x : H))) :
    Dense (Set.range fun x : conjDomain U D => conjOp U T x + c • (x : H)) := by
  have hset : (Set.range fun x : conjDomain U D => conjOp U T x + c • (x : H))
      = U.symm '' (Set.range fun x : D => T x + c • (x : H)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨T ⟨U (x : H), x.2⟩ + c • (U (x : H)), ⟨⟨U (x : H), x.2⟩, rfl⟩, ?_⟩
      simp [conjOp_apply]
    · rintro ⟨-, ⟨x, rfl⟩, rfl⟩
      have hmem : U.symm (x : H) ∈ conjDomain U D := by
        show U (U.symm (x : H)) ∈ D
        simp
      refine ⟨⟨U.symm (x : H), hmem⟩, ?_⟩
      have hT : T ⟨U (U.symm (x : H)), hmem⟩ = T x := by
        congr 1
        exact Subtype.ext (by simp)
      show U.symm (T ⟨U (U.symm (x : H)), hmem⟩) + c • U.symm (x : H)
          = U.symm (T x + c • (x : H))
      rw [hT]
      simp
  rw [hset]
  exact U.symm.surjective.denseRange.dense_image U.symm.continuous hd

