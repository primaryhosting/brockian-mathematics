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

lemma diagonal_real_sq (s : n → ℝ) :
    diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))
      = diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  ring

/-- A unitary conjugate of a nonnegative diagonal matrix is positive semidefinite. -/
