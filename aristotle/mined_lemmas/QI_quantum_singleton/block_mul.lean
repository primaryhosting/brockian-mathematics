import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/

theorem block_mul {R A B C : Type} [Fintype R] [DecidableEq R] [Fintype A] [Fintype B] [Fintype C]
    (M : Matrix A B ℂ) (N : Matrix B C ℂ) :
    (Matrix.of fun (p : R × A) (q : R × B) => if p.1 = q.1 then M p.2 q.2 else 0) *
      (Matrix.of fun (p : R × B) (q : R × C) => if p.1 = q.1 then N p.2 q.2 else 0) =
    Matrix.of fun (p : R × A) (q : R × C) => if p.1 = q.1 then (M * N) p.2 q.2 else 0 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h]

/-- The block-diagonal matrix with identity blocks is the identity. -/
