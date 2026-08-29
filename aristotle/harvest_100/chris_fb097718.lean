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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of the expectation value `⟪ψ, H ψ⟫` of a Hamiltonian `H` which is diagonal
in the orthonormal basis `b` with (real) eigenvalues `E`:
it is the weighted sum of the eigenvalues with weights the squared moduli of the
coefficients of `ψ` in that basis. -/
theorem inner_hamiltonian_eq_sum (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    ⟪ψ, H ψ⟫_ℂ = ∑ i, (E i : ℂ) * (‖⟪b i, ψ⟫_ℂ‖ ^ 2 : ℝ) := by
  have h1 : H ψ = ∑ i, ((E i : ℂ) * ⟪b i, ψ⟫_ℂ) • b i := by
    conv_lhs => rw [← b.sum_repr ψ]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [b.repr_apply_apply, map_smul, hH i, smul_smul, mul_comm]
  rw [h1, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_smul_right, ← inner_conj_symm (b i) ψ, mul_assoc, mul_comm ((starRingEnd ℂ) _),
    Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq, RCLike.norm_conj]

/-- The expectation value of a Hamiltonian `H`, diagonal in the orthonormal basis `b` with
eigenvalues `E`, is bounded below by `E₀ * ‖ψ‖ ^ 2` whenever `E₀` is a lower bound for the
eigenvalues. -/
theorem expectation_ge (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ) (E₀ : ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (hE : ∀ i, E₀ ≤ E i) (ψ : V) :
    E₀ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re := by
  have hnorm : ‖ψ‖ ^ 2 = ∑ i, ‖⟪b i, ψ⟫_ℂ‖ ^ 2 :=
    (OrthonormalBasis.sum_sq_norm_inner_right b ψ).symm
  have hre : (⟪ψ, H ψ⟫_ℂ).re = ∑ i, E i * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
    rw [inner_hamiltonian_eq_sum b H E hH ψ]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_right (hE i) (sq_nonneg _)

/-- **Variational bound.**  Let `H` be a Hamiltonian on a (finite-dimensional) complex inner
product space which is diagonalized by the orthonormal basis `b` with real eigenvalues `E`,
and let `E₀` be a lower bound for the eigenvalues (e.g. the ground-state energy).
Then for every nonzero state `ψ` the Rayleigh quotient satisfies

`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/
theorem variational_bound (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ) (E₀ : ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (hE : ∀ i, E₀ ≤ E i) (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re := by
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  have hself : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [hself, le_div_iff₀ hpos]
  exact expectation_ge b H E E₀ hH hE ψ

end QPhys

