import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open Module Module.End LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- If `A` and `B` commute, then `B` maps each eigenspace of `A` into itself. -/

lemma mapsTo_eigenspace_of_commute {A B : E →ₗ[ℂ] E} (hAB : A ∘ₗ B = B ∘ₗ A) (mu : ℂ) :
    ∀ v ∈ eigenspace A mu, B v ∈ eigenspace A mu := by
  intro v hv
  rw [mem_eigenspace_iff] at hv ⊢
  have h1 : A (B v) = B (A v) := congrArg (fun f => f v) hAB
  rw [h1, hv, map_smul]

omit [FiniteDimensional ℂ E] in
/-- An eigenvalue of a symmetric operator is real (equal to the coercion of its real part). -/
