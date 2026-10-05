import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open NormedSpace

/-- In a complex Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem lieb_robinson_zero_velocity (H A B : 𝒜) (t : ℝ)
    (hHB : H * B = B * H) (hAB : A * B = B * A) :
    heisenberg H t A * B - B * heisenberg H t A = 0 := by
  have hsm : ∀ c : ℂ, Commute (c • H) B := by
    intro c
    exact Commute.smul_left (show Commute H B from hHB) c
  have hU : Commute (propagator H t) B := (hsm _).exp_left
  have hV : Commute (propagator H (-t)) B := (hsm _).exp_left
  have key : heisenberg H t A * B = B * heisenberg H t A := by
    set U := propagator H t
    set V := propagator H (-t)
    calc U * A * V * B = U * A * (V * B) := by rw [mul_assoc]
      _ = U * A * (B * V) := by rw [hV.eq]
      _ = U * (A * B) * V := by simp only [mul_assoc]
      _ = U * (B * A) * V := by rw [hAB]
      _ = U * B * (A * V) := by simp only [mul_assoc]
      _ = B * U * (A * V) := by rw [hU.eq]
      _ = B * (U * A * V) := by simp only [mul_assoc]
  rw [key, sub_self]

end CStar

end Frontier

/-! ### Sanity check: the hypotheses are satisfiable

The bound applies, for instance, to the algebra of bounded operators on the (finite-dimensional)
Hilbert space of a two-spin system, which is the standard setting for spin dynamics. -/

namespace Frontier

section Example

/-- The state space of two spin-1/2 particles. -/
abbrev TwoSpins : Type := EuclideanSpace ℂ (Fin 4)

noncomputable example (H A B : TwoSpins →L[ℂ] TwoSpins) (hH : IsSelfAdjoint H) (t : ℝ)
    (hAB : A * B = B * A) :
    ‖heisenberg H t A * B - B * heisenberg H t A‖ ≤
      2 * ‖A‖ * ‖B‖ * min 1 (2 * (Real.exp (‖H‖ * |t|) - 1)) :=
  lieb_robinson H A B hH t hAB

end Example

end Frontier

