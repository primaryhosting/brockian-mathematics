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
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Extending a partial isometry -/

/-- If `‖p x‖ = ‖m x‖` for all `x`, then the assignment `p x ↦ m x` extends to a global
linear isometry `w` of the (finite dimensional) space, i.e. `w (p x) = m x` for all `x`. -/

lemma norm_sq_toEuclideanLin (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 = (inner ℂ x (Matrix.toEuclideanLin (Mᴴ * M) x)).re := by
  rw [toEuclideanLin_mul', Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- **Polar decomposition**: every square complex matrix factors as `M = U * √(Mᴴ M)` with
`U` unitary. -/
