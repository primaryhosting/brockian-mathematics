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
theorem norm_sq_eq_sum_inner_sq (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]

/-- **Variational bound (Rayleigh–Ritz).**  Let `H` be a self-adjoint (symmetric) Hamiltonian
on a finite-dimensional complex Hilbert space, and let `E₀` be a lower bound for all of its
eigenvalues (e.g. the ground-state energy).  Then for every nonzero state `ψ` the Rayleigh
quotient satisfies
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/
theorem variational_bound {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ hH.eigenvalues hn i)
    (ψ : E) (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ) : ℂ).re / (inner ℂ ψ ψ : ℂ).re := by
  set b := hH.eigenvectorBasis hn with hb
  set c : Fin n → ℝ := fun i => ‖inner ℂ (b i) ψ‖ ^ 2 with hc
  have hnormsq : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hnorm : (inner ℂ ψ ψ : ℂ).re = ∑ i, c i := by
    rw [hnormsq]
    exact norm_sq_eq_sum_inner_sq b ψ
  have hnum : (inner ℂ ψ (H ψ) : ℂ).re = ∑ i, hH.eigenvalues hn i * c i := by
    rw [inner_apply_eq_sum_eigenvalues hH hn ψ, Complex.ofReal_re]
  have hcnonneg : ∀ i ∈ Finset.univ, 0 ≤ c i := fun i _ => by positivity
  have hpos : 0 < ∑ i, c i := by
    rw [← hnorm, hnormsq]
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [hnum, hnorm, le_div_iff₀ hpos, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE₀ i) (hcnonneg i (Finset.mem_univ i))

end QPhys

