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

lemma purification_matrix {ρ : Matrix n n ℂ} {ψ : EuclideanSpace ℂ (n × n)}
    (h : IsPurification ρ ψ) :
    (Matrix.of fun i k => ψ (i, k)) * (Matrix.of fun i k => ψ (i, k))ᴴ = ρ := by
  ext i j
  rw [Matrix.mul_apply]
  simpa [Matrix.conjTranspose_apply, RCLike.star_def] using h i j

omit [DecidableEq n] in
/-- The vector of coefficients of `A` is a purification of `A * Aᴴ`. -/
