import Mathlib
/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem amo_int_shift (lam alpha theta : ℝ) (k m : ℤ) :
    amo lam (alpha - k) (theta - m) = amo lam alpha theta := by
  refine amo_congr fun n => ?_
  have hcos : Real.cos (2 * π * (theta - m + n * (alpha - k)))
      = Real.cos (2 * π * (theta + n * alpha)) := by
    have : 2 * π * (theta - m + n * (alpha - k))
        = 2 * π * (theta + n * alpha) - ((m + n * k : ℤ) : ℝ) * (2 * π) := by
      push_cast
      ring
    rw [this, Real.cos_sub_int_mul_two_pi]
  simp [amoPotential, hcos]

/-- Flipping the sign of the coupling amounts to a half-period shift of the phase. -/
