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

theorem unique_selfAdjoint_extension {A : E →ₗ.[ℂ] E} (hA : IsEssentiallySelfAdjoint A) :
    ∃! B : E →ₗ.[ℂ] E, IsSelfAdjoint B ∧ A ≤ B := by
  obtain ⟨hdense, hsym, hsa⟩ := hA
  refine ⟨A.adjoint, ⟨hsa, hsym.le_adjoint hdense⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  have hBd : Dense (B.domain : Set E) := hB.dense_domain
  have h1 : B ≤ A.adjoint := by
    have := adjoint_le_adjoint_of_le hdense hAB
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at this
  have h2 : A.adjoint ≤ B := by
    have := adjoint_le_adjoint_of_le hBd h1
    rwa [LinearPMap.isSelfAdjoint_def.mp hB, LinearPMap.isSelfAdjoint_def.mp hsa] at this
  exact le_antisymm h1 h2

/-! ## The minimal diagonal operator attached to a Hilbert basis -/

variable (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)

/-- The minimal operator with eigenbasis `b` and (real) eigenvalues `lam`: it is defined on the
algebraic span of the basis vectors, where it acts by `b i ↦ lam i • b i`. -/
