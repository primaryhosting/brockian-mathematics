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

theorem exists_rayleigh_eq_ground_energy {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = m + 1)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) :
    ∃ ψ : E, ψ ≠ 0 ∧ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 = hH.eigenvalues hn (Fin.last m) := by
  set b := hH.eigenvectorBasis hn with hb
  refine ⟨b (Fin.last m), b.toBasis.ne_zero _, ?_⟩
  have hnorm : ‖b (Fin.last m)‖ = 1 := b.norm_eq_one _
  rw [hb, hH.apply_eigenvectorBasis hn (Fin.last m), inner_smul_right]
  simp [hnorm, ← hb, inner_self_eq_norm_sq_to_K]

end QPhys

