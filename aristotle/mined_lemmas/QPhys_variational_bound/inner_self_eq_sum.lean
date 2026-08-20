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

theorem inner_self_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    (inner ℂ ψ ψ).re = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [b.sum_sq_norm_inner_right ψ, inner_self_re]

/-- **Variational bound (Rayleigh–Ritz).**  Let `H` be a Hamiltonian on a complex inner product
space admitting an orthonormal eigenbasis `b` with real eigenvalues `E i`, and let `E0` be a
lower bound for all the eigenvalues (e.g. the ground-state energy).  Then for every nonzero
state `ψ` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E0`. -/
