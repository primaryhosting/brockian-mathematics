/-
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
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

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n]

/-- The quadratic form (sesquilinear form evaluated on the diagonal) attached to a complex
matrix `M`: `qf M x = ⟪x, M x⟫`, where `M x` is the matrix-vector product. -/
noncomputable def qf (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℂ :=
  inner ℂ x (WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)))

/-- Explicit coordinate formula: `qf M x = ∑ i, ∑ j, conj (x i) * M i j * x j`. -/
theorem qf_apply (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    qf M x = ∑ i, ∑ j, star (x i) * M i j * x j := by
  simp only [qf, PiLp.inner_apply, Matrix.mulVec, dotProduct, RCLike.inner_apply,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [starRingEnd_apply]
    ring

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add (M N : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf, Matrix.add_mulVec]

end Zeta23Redux.LinAlg

