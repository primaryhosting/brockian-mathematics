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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem adjoint_le_adjoint_of_le {A B : E →ₗ.[ℂ] E} (hA : Dense (A.domain : Set E))
    (hAB : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hsub : (A.domain : Set E) ⊆ (B.domain : Set E) := fun x hx => hAB.1 hx
  have hB : Dense (B.domain : Set E) := hA.mono hsub
  refine LinearPMap.IsFormalAdjoint.le_adjoint hA ?_
  intro x y
  have hx : (x : E) ∈ B.domain := hAB.1 x.2
  have hAx : A x = B ⟨(x : E), hx⟩ := hAB.2 rfl
  rw [hAx]
  exact (LinearPMap.adjoint_isFormalAdjoint hB).symm ⟨(x : E), hx⟩ y

/-- An essentially self-adjoint operator has exactly one self-adjoint extension. -/
