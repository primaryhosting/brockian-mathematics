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

lemma isPurification_toLp (A : Matrix n n ℂ) :
    IsPurification (A * Aᴴ) (WithLp.toLp 2 (fun p : n × n => A p.1 p.2)) := by
  intro i j
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply, RCLike.star_def]

omit [DecidableEq n] in
/-- The overlap of two purifications is the Hilbert-Schmidt inner product of their
coefficient matrices. -/
