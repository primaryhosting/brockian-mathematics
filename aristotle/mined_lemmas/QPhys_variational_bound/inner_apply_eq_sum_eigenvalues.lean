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

theorem inner_apply_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (ψ : E) :
    (inner ℂ ψ (T ψ)) =
      ((∑ i, hT.eigenvalues hn i * ‖inner ℂ (hT.eigenvectorBasis hn i) ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner ψ (T ψ)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hT (hT.eigenvectorBasis hn i) ψ, hT.apply_eigenvectorBasis, inner_smul_left,
    ← inner_conj_symm ψ (hT.eigenvectorBasis hn i), mul_left_comm, Complex.conj_mul']
  simp

omit [FiniteDimensional ℂ E] in
/-- Parseval: the squared norm is the sum of the squared moduli of the coefficients. -/
