import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

set_option grind.warning false

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

lemma hasDerivAt_cos_affine (c d : ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.cos (2 * π * (c + s * d)))
      (-(2 * π * d) * Real.sin (2 * π * (c + t * d))) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * (c + s * d)) (2 * π * d) t := by
    have := (((hasDerivAt_id t).mul_const d).const_add c).const_mul (2 * π)
    simpa using this
  have := (Real.hasDerivAt_cos (2 * π * (c + t * d))).comp t h1
  simpa [mul_comm] using this

