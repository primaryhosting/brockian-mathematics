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

theorem expectation_ge (H : E →ₗ[ℂ] E) (b : OrthonormalBasis n ℂ E) (lam : n → ℝ) (E0 : ℝ)
    (hH : ∀ i, H (b i) = (lam i : ℂ) • b i) (hE0 : ∀ i, E0 ≤ lam i) (psi : E) :
    E0 * ‖psi‖ ^ 2 ≤ (inner ℂ psi (H psi) : ℂ).re := by
  have hre : (inner ℂ psi (H psi) : ℂ).re = ∑ i, lam i * ‖b.repr psi i‖ ^ 2 := by
    rw [inner_H_eq_sum_eigenvalues H b lam hH]
    push_cast
    simp [← Complex.ofReal_pow]
  rw [hre, norm_sq_eq_sum_repr_sq b psi, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

/-- **Variational bound (Rayleigh–Ritz).**  Let `H` be a linear operator on a complex inner
product space admitting an orthonormal eigenbasis `b` with real eigenvalues `lam`, and let
`E0` be a lower bound for all eigenvalues (e.g. the ground-state energy).  Then for every
nonzero state `ψ`, the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E0`. -/
