/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

section

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an eigenbasis `b` of `H` with eigenvalues `E`. -/

theorem variational_bound_mul_normSq (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i) (ψ : V) :
    E₀ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re := by
  rw [re_inner_apply_eq_sum b H E hH ψ, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

/-- **The ground-state variational bound.**
Let `H` be a (linear) Hamiltonian on a complex inner product space possessing an orthonormal
eigenbasis `b` with real eigenvalues `E i`, and let `E₀` be a lower bound for the spectrum
(e.g. the ground-state energy). Then for every nonzero state `ψ`,
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/
