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

noncomputable def ddpsi (x : ℝ) : ℂ := ((x ^ 2 - 1) * Real.exp (-x ^ 2 / 2) : ℝ)

/-- The harmonic potential. -/
