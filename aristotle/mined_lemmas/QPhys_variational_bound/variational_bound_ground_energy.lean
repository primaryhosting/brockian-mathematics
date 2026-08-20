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

set_option grind.warning false

namespace QPhys

/-- **Variational principle** (ground-state variational bound).

Let `H` be a Hamiltonian, i.e. a self-adjoint (symmetric) linear operator on a
finite-dimensional complex inner product space `E`, and let `E0` be a lower bound for the
spectrum of `H` (for instance the ground-state energy, the smallest eigenvalue).  Then for
every nonzero state `ψ` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E0`.

Here `⟨ψ|H|ψ⟩` is `re ⟪ψ, H ψ⟫` (the quantity is real since `H` is self-adjoint) and
`⟨ψ|ψ⟩ = ‖ψ‖ ^ 2`. -/

theorem variational_bound_ground_energy {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = m + 1)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (ψ : E) (hψ : ψ ≠ 0) :
    (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 ≥ hH.eigenvalues hn (Fin.last m) :=
  variational_bound hn H hH _ (ground_energy_le_of_hasEigenvalue hn H hH) ψ hψ

/-- The variational bound is sharp: the ground-state energy is attained by an eigenvector. -/
