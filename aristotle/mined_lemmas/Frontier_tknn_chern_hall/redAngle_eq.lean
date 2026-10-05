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

lemma redAngle_eq (x : ℝ) :
    redAngle x = x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℤ) := rfl

variable {N M : ℕ}

/-- The discrete (lattice) Berry curvature of a `U(1)` gauge field on the Brillouin torus.

The Brillouin zone is discretized as `ZMod N × ZMod M`; `A1` and `A2` are the Berry phases
(link angles) of the occupied Bloch state along the two lattice directions.  The curvature of
a plaquette is the total phase picked up going around it, reduced to the principal branch —
this is the Fukui–Hatsugai–Suzuki lattice field strength. -/
