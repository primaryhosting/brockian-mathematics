/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real
open Finset

namespace Frontier

/-- The representative of an angle `x` modulo `2π` obtained by subtracting the nearest
multiple of `2π`.  This is the "principal branch" of the logarithm of `exp (i x)`. -/

noncomputable def redAngle (x : ℝ) : ℝ := x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℤ)

