import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

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

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/

theorem sum_normSq_eq_trace_reducedState {n m : Type*} [Fintype n] [Fintype m] (ψ : n × m → ℂ) :
    ((∑ p : n × m, ‖ψ p‖ ^ 2 : ℝ) : ℂ) = (reducedState ψ).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, reducedState, Matrix.of_apply]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq _).symm

/-- A purification of a mixed state is a unit vector. -/
