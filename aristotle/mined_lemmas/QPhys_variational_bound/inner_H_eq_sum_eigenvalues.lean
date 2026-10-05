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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {n : Type*} [Fintype n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expansion of the expectation value `⟨ψ|H|ψ⟩` in an eigenbasis of `H`:
if `H (b i) = lam i • b i` for an orthonormal basis `b`, then
`⟨ψ|H|ψ⟩ = ∑ i, lam i * |⟨b i, ψ⟩|²`. -/

theorem inner_H_eq_sum_eigenvalues (H : E →ₗ[ℂ] E) (b : OrthonormalBasis n ℂ E) (lam : n → ℝ)
    (hH : ∀ i, H (b i) = (lam i : ℂ) • b i) (psi : E) :
    (inner ℂ psi (H psi) : ℂ) = ∑ i, (lam i : ℂ) * (‖b.repr psi i‖ : ℂ) ^ 2 := by
  have hHpsi : H psi = ∑ i, (b.repr psi i * (lam i : ℂ)) • b i := by
    conv_lhs => rw [← b.sum_repr psi]
    rw [map_sum]
    simp only [map_smul, hH, smul_smul]
  rw [hHpsi, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right]
  have h : (inner ℂ psi (b i) : ℂ) = starRingEnd ℂ (b.repr psi i) := by
    rw [b.repr_apply_apply, ← inner_conj_symm]
  rw [h, mul_right_comm, Complex.mul_conj', mul_comm]

/-- Parseval: the squared norm is the sum of squared moduli of the coefficients. -/
