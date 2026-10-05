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

noncomputable def euclideanHomeomorphPi : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).toHomeomorph

/-- A closed box `[-R, R]^n` in `ℝ^n` is compact: it is a finite product of compact
intervals, hence compact in the product topology, which agrees with the Euclidean topology. -/
