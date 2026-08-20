import Mathlib

/-!
# The variational principle (Rayleigh–Ritz ground-state bound)

For a self-adjoint (symmetric) Hamiltonian `H` on a finite-dimensional complex inner product
space, and any nonzero state `ψ`, the Rayleigh quotient `⟪ψ, H ψ⟫ / ⟪ψ, ψ⟫` is bounded below
by the ground-state energy `E₀`, i.e. the smallest eigenvalue of `H`.
-/

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E}

/-- The (real part of the) expectation value `⟪ψ, H ψ⟫` expanded in the eigenbasis of `H`. -/

theorem norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖b.repr ψ i‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Variational principle.**  Let `H` be a self-adjoint operator (Hamiltonian) on a
finite-dimensional complex inner product space `E` of dimension `n > 0`, and let
`E₀ = ⨅ i, hH.eigenvalues hn i` be its ground-state energy (the smallest eigenvalue).
Then for every nonzero state `ψ`, the Rayleigh quotient `⟪ψ, H ψ⟫ / ⟪ψ, ψ⟫` is at least `E₀`. -/
