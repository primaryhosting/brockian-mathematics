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

lemma norm_trace_eq_re {P : Matrix n n ℂ} (hP : P.PosSemidef) : ‖P.trace‖ = P.trace.re := by
  have h := hP.trace_nonneg
  rw [Complex.le_def] at h
  simp only [Complex.zero_re, Complex.zero_im] at h
  rw [Complex.norm_def, Complex.normSq_apply, ← h.2]
  simp [Real.sqrt_mul_self h.1]

/-- If `P` is positive semidefinite and `V` is unitary then `|tr (V P)| ≤ tr P`. -/
