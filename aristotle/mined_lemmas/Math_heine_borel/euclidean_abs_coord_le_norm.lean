import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
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

open Metric Bornology

namespace Math

variable {n : ℕ}

/-- Each coordinate of a vector in `ℝ^n` is bounded in absolute value by its Euclidean norm. -/

theorem euclidean_abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le (p := 2) x i

/-- `ℝ^n` with the Euclidean norm is homeomorphic to the product `Fin n → ℝ`. -/
