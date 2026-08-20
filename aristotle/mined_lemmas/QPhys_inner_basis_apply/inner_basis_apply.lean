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

lemma inner_basis_apply (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) (i : Fin n) :
    inner ℂ (b i) (H ψ) = (E i : ℂ) * inner ℂ (b i) ψ := by
  conv_lhs => rw [← b.sum_repr' ψ]
  rw [map_sum]
  simp only [map_smul, hE, smul_smul, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [mul_comm]
  · intro j _ hj
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [Ne.symm hj]
  · intro h; simp at h

/-- Expansion of the expectation value in the eigenbasis. -/
