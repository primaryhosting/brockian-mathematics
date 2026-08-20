import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

lemma conj_expect_of_isSymm {A : H →ₗ[ℂ] H} (hA : IsSymm A) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  rw [expect, inner_conj_symm]
  exact hA ψ ψ

/-- Key identity: the expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` for the
centered vectors `u = (A - ⟨A⟩)ψ`, `v = (B - ⟨B⟩)ψ`. -/
