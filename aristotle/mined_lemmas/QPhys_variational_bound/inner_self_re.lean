/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QPhys

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- `⟨ψ|ψ⟩` is real and equals `‖ψ‖ ^ 2`. -/

theorem inner_self_re (ψ : V) : (inner ℂ ψ ψ).re = ‖ψ‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  simpa using this

/-- **Expansion of the expectation value.**  If `b` is an orthonormal eigenbasis of the
Hamiltonian `H` with real eigenvalues `E i`, then the expectation value `⟨ψ|H|ψ⟩` equals the
eigenvalue-weighted sum of the squared moduli of the expansion coefficients `⟪b i, ψ⟫`. -/
