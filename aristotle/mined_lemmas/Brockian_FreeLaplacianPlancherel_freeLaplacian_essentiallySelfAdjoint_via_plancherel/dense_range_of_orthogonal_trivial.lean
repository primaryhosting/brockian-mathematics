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

lemma dense_range_of_orthogonal_trivial [CompleteSpace H] {D : Submodule ℂ H}
    (T : D →ₗ[ℂ] H) (c : ℂ)
    (h : ∀ z : H, (∀ x : D, ⟪T x + c • (x : H), z⟫ = 0) → z = 0) :
    Dense (Set.range fun x : D => T x + c • (x : H)) := by
  have hrange : (Set.range fun x : D => T x + c • (x : H))
      = ((LinearMap.range (T + c • D.subtype) : Submodule ℂ H) : Set H) := by
    rw [LinearMap.coe_range]; rfl
  rw [hrange]
  refine dense_of_orthogonal_trivial (fun z hz => h z fun x => ?_)
  exact hz _ ⟨x, rfl⟩

end Abstract

/-! ## Unitary conjugation -/

section Conjugation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the operator conjugated by a unitary `U`. -/
