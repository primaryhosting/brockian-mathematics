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

lemma norm_vecHS (A : Matrix n n ℂ) : ‖vecHS A‖ = Real.sqrt ((Aᴴ * A).trace.re) := by
  rw [← Real.sqrt_sq (norm_nonneg (vecHS A)), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecHS]
  rfl

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the Hilbert–Schmidt (Frobenius) inner product on matrices. -/
