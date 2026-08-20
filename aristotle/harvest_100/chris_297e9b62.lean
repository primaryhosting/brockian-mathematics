import Mathlib

/-!
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Redux
namespace LinAlg

/-- The quadratic form (sesquilinear form) associated to a complex matrix `M`,
evaluated at a vector `x` of Euclidean space: `qf M x = ∑ i, ∑ j, conj (x i) * M i j * x j`. -/
noncomputable def qf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (x i) * M i j * x j

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    qf (M + N) x = qf M x + qf N x := by
  simp only [qf, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end LinAlg
end Zeta23Redux

