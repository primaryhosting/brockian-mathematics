/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is written as a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 requires all `import` commands to come
-- before any command, and a module docstring counts as a command.)
import Mathlib

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

namespace QC

open Complex

/-- A (normalized) pure qubit state vector: a unit vector of `ℂ²`. -/

def PureQubit : Type := Quotient phaseSetoid

/-- The 2-sphere `S² ⊆ ℝ³`. -/
