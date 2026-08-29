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

lemma cycRoot_quad (k : ℕ) :
    (cycRoot m ^ k) ^ 2 + 1 = ((2 * Real.cos (k * cycAngle m) : ℝ) : ℂ) * cycRoot m ^ k := by
  rw [cycRoot_pow_eq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  have h : (Real.cos ((k : ℝ) * cycAngle m) : ℂ) ^ 2
      + (Real.sin ((k : ℝ) * cycAngle m) : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.cos_sq_add_sin_sq ((k : ℝ) * cycAngle m))
  linear_combination -h + (Real.sin ((k : ℝ) * cycAngle m) : ℂ) ^ 2 * Complex.I_sq

