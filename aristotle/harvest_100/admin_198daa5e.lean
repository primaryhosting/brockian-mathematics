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
theorem inner_H_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (E : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    (inner ℂ ψ (H ψ)).re = ∑ i, E i * ‖inner ℂ (b i) ψ‖ ^ 2 := by
  have hHψ : H ψ = ∑ i, ((E i : ℂ) * inner ℂ (b i) ψ) • b i := by
    conv_lhs => rw [← b.sum_repr' ψ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hH i, smul_smul, mul_comm]
  rw [hHψ, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (inner ℂ (b i) ψ) * (starRingEnd ℂ) (inner ℂ (b i) ψ)
      = ((‖inner ℂ (b i) ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [inner_smul_right, ← inner_conj_symm ψ (b i), mul_assoc, hc, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **Expansion of the squared norm.**  `⟨ψ|ψ⟩` is the sum of the squared moduli of the
expansion coefficients of `ψ` in the orthonormal basis `b` (Parseval's identity). -/
theorem inner_self_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    (inner ℂ ψ ψ).re = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [b.sum_sq_norm_inner_right ψ, inner_self_re]

/-- **Variational bound (Rayleigh–Ritz).**  Let `H` be a Hamiltonian on a complex inner product
space admitting an orthonormal eigenbasis `b` with real eigenvalues `E i`, and let `E0` be a
lower bound for all the eigenvalues (e.g. the ground-state energy).  Then for every nonzero
state `ψ` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E0`. -/
theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (E : Fin n → ℝ)
    (E0 : ℝ) (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (hE0 : ∀ i, E0 ≤ E i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E0 ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hpos : 0 < (inner ℂ ψ ψ).re := by
    rw [inner_self_re]
    exact pow_pos (norm_pos_iff.mpr hψ) 2
  rw [le_div_iff₀ hpos, inner_self_eq_sum b ψ, inner_H_eq_sum b H E hH ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

/-- The Rayleigh quotient of an eigenstate `b i` is exactly its eigenvalue `E i`; hence the
variational bound is attained. -/
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
theorem variational_bound_isLeast [Nonempty (Fin n)] (b : OrthonormalBasis (Fin n) ℂ V)
    (H : V →ₗ[ℂ] V) (E : Fin n → ℝ) (hH : ∀ i, H (b i) = (E i : ℂ) • b i) :
    IsLeast {r : ℝ | ∃ ψ : V, ψ ≠ 0 ∧ r = (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re}
      (Finset.univ.inf' Finset.univ_nonempty E) := by
  constructor
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin n)) E
    refine ⟨b i, ?_, ?_⟩
    · simpa using b.orthonormal.ne_zero i
    · rw [rayleigh_quotient_eigenvector b H E hH i, hi]
  · rintro r ⟨ψ, hψ, rfl⟩
    exact variational_bound b H E _ hH (fun i => Finset.inf'_le E (Finset.mem_univ i)) ψ hψ

end QPhys

