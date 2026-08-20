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

namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨T⟩_ψ = ⟪ψ, T ψ⟫` of an observable `T` in the state `ψ`. -/

lemma conj_expect (T : H →ₗ[ℂ] H) (psi : H)
    (hT : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ) :
    conj (expect T psi) = expect T psi := by
  unfold expect
  rw [inner_conj_symm, hT]

/-- Expanding the inner product of the two centred vectors. -/
