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

lemma cycRoot_pow_eq (k : ℕ) :
    cycRoot m ^ k = Complex.exp ((k * cycAngle m : ℝ) * Complex.I) := by
  unfold cycRoot cycAngle
  rw [← Complex.exp_nat_mul]
  congr 1
  have h : ((m + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

