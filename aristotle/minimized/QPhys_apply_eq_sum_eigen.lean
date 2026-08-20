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

lemma apply_eq_sum_eigen (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    H ψ = ∑ i, ((E i : ℂ) * ⟪b i, ψ⟫_ℂ) • b i := by
  conv_lhs => rw [← b.sum_repr' ψ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hH i, smul_smul, mul_comm]

/-- The expectation value `⟨ψ|H|ψ⟩` is the eigenvalue-weighted sum of the squared
moduli of the expansion coefficients of `ψ` in the eigenbasis. -/
