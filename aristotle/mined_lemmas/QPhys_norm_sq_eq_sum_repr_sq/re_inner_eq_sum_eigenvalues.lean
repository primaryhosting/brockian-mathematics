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

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `‖ψ‖²` in the coefficients of `ψ` with respect to an orthonormal basis
(Parseval's identity for a finite orthonormal basis). -/

lemma re_inner_eq_sum_eigenvalues (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (Ev : ι → ℝ)
    (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (ψ : V) :
    (inner ℂ ψ (H ψ)).re = ∑ i, Ev i * ‖(b.repr ψ).ofLp i‖ ^ 2 := by
  have hψ : ∑ i, (b.repr ψ).ofLp i • b i = ψ := b.sum_repr ψ
  have hcinner : ∀ i, inner ℂ ψ (b i) = (starRingEnd ℂ) ((b.repr ψ).ofLp i) := by
    intro i
    rw [b.repr_apply_apply, inner_conj_symm]
  have h2 : H ψ = ∑ i, ((b.repr ψ).ofLp i * (Ev i : ℂ)) • b i := by
    conv_lhs => rw [← hψ]
    rw [map_sum]
    simp only [map_smul, hH, smul_smul]
  have key : inner ℂ ψ (H ψ) = ∑ i, ((Ev i : ℂ) * ((‖(b.repr ψ).ofLp i‖ : ℝ) : ℂ) ^ 2) := by
    rw [h2, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, hcinner i]
    rw [show ((b.repr ψ).ofLp i * (Ev i : ℂ)) * (starRingEnd ℂ) ((b.repr ψ).ofLp i)
        = (Ev i : ℂ) * ((b.repr ψ).ofLp i * (starRingEnd ℂ) ((b.repr ψ).ofLp i)) by ring,
      Complex.mul_conj']
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Variational bound (Rayleigh–Ritz).**

Let `H` be a Hamiltonian on a finite-dimensional complex inner product space which is diagonal
in an orthonormal basis `b` with real eigenvalues `Ev`, and let `E₀` be a lower bound for the
spectrum (the ground-state energy). Then for every nonzero state `ψ`, the Rayleigh quotient
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
