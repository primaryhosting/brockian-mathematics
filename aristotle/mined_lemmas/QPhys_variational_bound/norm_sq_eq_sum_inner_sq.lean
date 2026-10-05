import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace QPhys

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Expansion of the expectation value `⟪ψ, H ψ⟫` in the eigenbasis of a symmetric
(self-adjoint) Hamiltonian `H`: it equals `∑ᵢ Eᵢ |⟪bᵢ, ψ⟫|²`, in particular it is real. -/

theorem norm_sq_eq_sum_inner_sq (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]

/-- **Variational bound (Rayleigh–Ritz).**  Let `H` be a self-adjoint (symmetric) Hamiltonian
on a finite-dimensional complex Hilbert space, and let `E₀` be a lower bound for all of its
eigenvalues (e.g. the ground-state energy).  Then for every nonzero state `ψ` the Rayleigh
quotient satisfies
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/
