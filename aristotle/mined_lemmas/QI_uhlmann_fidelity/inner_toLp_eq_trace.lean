import Mathlib
/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Singular value decomposition -/

/-- Every square complex matrix admits a singular value decomposition
`M = U * diagonal s * V` with `U`, `V` unitary and `s` a nonnegative real vector. -/

lemma inner_toLp_eq_trace (A B : Matrix n n ℂ) :
    (inner ℂ (WithLp.toLp 2 (fun p : n × n => A p.1 p.2) : EuclideanSpace ℂ (n × n))
      (WithLp.toLp 2 (fun p : n × n => B p.1 p.2)) : ℂ) = (Aᴴ * B).trace := by
  rw [Matrix.trace_mul_comm]
  simp [PiLp.inner_apply, RCLike.inner_apply, Matrix.trace, Matrix.mul_apply, Matrix.diag,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]

omit [Fintype n] [DecidableEq n] in
