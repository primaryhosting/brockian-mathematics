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

lemma norm_trace_unitary_mul_le {P V : Matrix n n ℂ} (hP : P.PosSemidef) (hV : Vᴴ * V = 1) :
    ‖(V * P).trace‖ ≤ P.trace.re := by
  set S := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)
  have hSh : Sᴴ = S := hS.isHermitian.eq
  have key : (V * P).trace = (Sᴴ * (V * S)).trace := by
    rw [hSh, ← hSS, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h1 : (Sᴴ * S).trace = P.trace := by rw [hSh, hSS]
  have h2 : ((V * S)ᴴ * (V * S)).trace = P.trace := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V S, hV,
      Matrix.one_mul, hSh, hSS]
  have hcs := norm_trace_conjTranspose_mul_le S (V * S)
  rw [h1, h2] at hcs
  rw [key]
  calc ‖(Sᴴ * (V * S)).trace‖ ≤ Real.sqrt (P.trace.re) * Real.sqrt (P.trace.re) := hcs
    _ = P.trace.re := Real.mul_self_sqrt (re_trace_nonneg hP)

/-! ## Fidelity and Uhlmann's theorem -/

/-- The (Uhlmann) fidelity of two positive semidefinite matrices,
`F(ρ, σ) = tr √(√ρ σ √ρ)`. -/
