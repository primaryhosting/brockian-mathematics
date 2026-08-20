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

/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped ComplexConjugate

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Action of the Hamiltonian on a basis vector, tested against `ψ`:
if `H` has orthonormal eigenbasis `b` with (real) eigenvalues `E`, then
`⟪bᵢ, Hψ⟫ = Eᵢ ⟪bᵢ, ψ⟫`. -/

lemma inner_self_expansion (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    inner ℂ ψ (H ψ) = ∑ i, ((E i * ‖inner ℂ (b i) ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner ψ (H ψ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_basis_apply b H E hE ψ i, ← inner_conj_symm (b i) ψ]
  push_cast
  rw [RCLike.norm_conj, mul_comm (inner ℂ ψ (b i)), mul_assoc,
    mul_comm ((starRingEnd ℂ) (inner ℂ ψ (b i))), Complex.mul_conj']

/-- Norm squared expanded in the eigenbasis. -/
