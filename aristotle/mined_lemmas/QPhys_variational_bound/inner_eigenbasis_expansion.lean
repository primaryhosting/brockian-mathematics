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

open Module

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Expansion of the expectation value `⟪ψ, H ψ⟫` in an orthonormal eigenbasis `b` of `H`
with (real) eigenvalues `E`. -/

theorem inner_eigenbasis_expansion {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hb : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    inner ℂ ψ (H ψ)
      = ∑ i, (E i : ℂ) * (starRingEnd ℂ ((b.repr ψ).ofLp i) * (b.repr ψ).ofLp i) := by
  rw [show H ψ = ∑ i, ((E i : ℂ) * (b.repr ψ).ofLp i) • b i from ?_]
  · rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, ← inner_conj_symm, b.repr_apply_apply]
    ring
  · conv_lhs => rw [← b.sum_repr ψ]
    rw [map_sum]
    simp only [map_smul, hb, smul_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [FiniteDimensional ℂ V] in
/-- Parseval: the squared norm is the sum of the squared moduli of the coordinates in an
orthonormal basis. -/
