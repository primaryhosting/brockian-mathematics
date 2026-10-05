import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma cos_cycAngle_mod (a : ℕ) :
    Real.cos ((a % (m + 3) : ℕ) * cycAngle m) = Real.cos (a * cycAngle m) := by
  have key : (a : ℝ) * cycAngle m
      = ((a % (m + 3) : ℕ) : ℝ) * cycAngle m + ((a / (m + 3) : ℕ) : ℝ) * (2 * Real.pi) := by
    have h := Nat.mod_add_div a (m + 3)
    have hc : ((a % (m + 3) : ℕ) : ℝ) + ((m : ℝ) + 3) * ((a / (m + 3) : ℕ) : ℝ) = a := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
    rw [← hc, ← cycAngle_mul (m := m)]
    ring
  rw [key, Real.cos_add_nat_mul_two_pi]

/-- The action of the Laplacian of the cycle graph on a vector. -/
