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

theorem inner_apply_re_eq_sum (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n) (ψ : E) :
    (⟪ψ, H ψ⟫_ℂ).re
      = ∑ i, hH.eigenvalues hn i * ‖(hH.eigenvectorBasis hn).repr ψ i‖ ^ 2 := by
  set b := hH.eigenvectorBasis hn with hb
  have h1 : ⟪ψ, H ψ⟫_ℂ = ⟪b.repr ψ, b.repr (H ψ)⟫_ℂ := (b.repr.inner_map_map ψ (H ψ)).symm
  rw [h1, PiLp.inner_apply]
  simp only [hb, hH.eigenvectorBasis_apply_self_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  rw [RCLike.inner_apply, hz]
  simp [Complex.mul_re]
  ring

omit [FiniteDimensional ℂ E] in
/-- Parseval, restated for an arbitrary orthonormal basis. -/
