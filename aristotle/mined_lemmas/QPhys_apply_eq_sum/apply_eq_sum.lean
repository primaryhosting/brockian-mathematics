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

/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an orthonormal eigenbasis of `H`. -/

lemma apply_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (psi : V) :
    H psi = ∑ i, ((mu i : ℂ) * ⟪b i, psi⟫_ℂ) • b i := by
  conv_lhs => rw [← b.sum_repr psi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hH i, smul_smul, b.repr_apply_apply]
  ring_nf

/-- The `i`-th coefficient of `H ψ` is `μ i` times the `i`-th coefficient of `ψ`. -/
