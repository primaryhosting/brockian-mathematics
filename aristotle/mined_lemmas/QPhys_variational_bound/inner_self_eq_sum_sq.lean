/-!
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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open ComplexConjugate

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Conjugate times itself is the squared norm, as a complex number. -/

lemma inner_self_eq_sum_sq (b : OrthonormalBasis ι ℂ V) (ψ : V) :
    (inner ℂ ψ ψ : ℂ) = ∑ i, ((‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner ψ ψ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← b.repr_apply_apply, ← inner_conj_symm (𝕜 := ℂ) (b i) ψ, ← b.repr_apply_apply,
    conj_mul_self]

/-- Expansion of `⟪ψ, Hψ⟫` in an orthonormal eigenbasis of `H`. -/
