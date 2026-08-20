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

theorem variational_bound (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re := by
  have hnorm : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [hnorm, le_div_iff₀ hpos]
  exact variational_bound_mul_normSq b H E hH E₀ hE₀ ψ

end

section Symmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Variational bound for a symmetric (self-adjoint) Hamiltonian.**
On a finite-dimensional complex Hilbert space, if `H` is symmetric and `E₀` is a lower bound
for all of its (necessarily real) eigenvalues — e.g. `E₀` is the ground-state energy — then
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀` for every nonzero state `ψ`.
The orthonormal eigenbasis is supplied by the finite-dimensional spectral theorem. -/
