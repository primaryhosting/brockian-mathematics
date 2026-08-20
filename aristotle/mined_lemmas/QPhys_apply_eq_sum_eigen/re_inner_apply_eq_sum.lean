/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

section

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an eigenbasis `b` of `H` with eigenvalues `E`. -/

lemma re_inner_apply_eq_sum (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    (⟪ψ, H ψ⟫_ℂ).re = ∑ i, E i * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
  rw [apply_eq_sum_eigen b H E hH ψ, inner_sum]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (b i) ψ]
  rw [mul_assoc, Complex.conj_mul', Complex.norm_conj]
  norm_cast

/-- **Variational bound (unnormalised form).** If `H` has an orthonormal eigenbasis with all
eigenvalues bounded below by `E₀`, then `E₀ ‖ψ‖² ≤ ⟨ψ|H|ψ⟩` for every state `ψ`. -/
