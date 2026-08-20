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
