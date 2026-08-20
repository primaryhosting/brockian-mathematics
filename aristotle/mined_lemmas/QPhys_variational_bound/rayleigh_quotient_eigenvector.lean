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

theorem rayleigh_quotient_eigenvector (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (i : Fin n) :
    (inner ℂ (b i) (H (b i))).re / (inner ℂ (b i) (b i)).re = E i := by
  have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
  have hinner : (inner ℂ (b i) (b i) : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b i), h1]
    norm_num
  have hd : (inner ℂ (b i) (b i)).re = 1 := by rw [hinner]; simp
  rw [hH i, inner_smul_right, hd, div_one, hinner, mul_one, Complex.ofReal_re]

/-- **Sharp form of the variational principle.**  The ground-state energy, i.e. the smallest
eigenvalue of `H`, is the least value of the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` over all
nonzero states `ψ`: it is a lower bound (the variational bound) and it is attained. -/
