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

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Finset

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of an inner product against a vector written in an orthonormal basis. -/

lemma apply_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (E : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (psi : V) :
    H psi = ∑ i, ((E i : ℂ) * inner ℂ (b i) psi) • b i := by
  conv_lhs => rw [← b.sum_repr psi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, hH i, smul_smul, b.repr_apply_apply, mul_comm]

/-- **Variational principle.** If `H` is a linear operator on a finite-dimensional complex
inner product space admitting an orthonormal eigenbasis `b` with (real) eigenvalues `E i`,
and `E₀` is a lower bound for all the eigenvalues (e.g. the ground-state energy), then for
every nonzero state `psi` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
