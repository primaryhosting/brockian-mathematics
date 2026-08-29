/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter MeasureTheory Topology Complex

namespace Phys

/-- `‖z‖ ^ 2` in terms of the real and imaginary parts of `z`. -/

noncomputable def dpsi (x : ℝ) : ℂ := ((-x) * Real.exp (-x ^ 2 / 2) : ℝ)

/-- Second derivative of the ground state. -/
