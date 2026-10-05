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

theorem sum_berryCurvature_eq [NeZero N] [NeZero M] (A1 A2 : ZMod N × ZMod M → ℝ) :
    ∃ C : ℤ, ∑ k : ZMod N × ZMod M, berryCurvature A1 A2 k = 2 * Real.pi * (C : ℝ) := by
  classical
  refine ⟨- ∑ k : ZMod N × ZMod M,
    round ((A1 k + A2 (k.1 + 1, k.2) - A1 (k.1, k.2 + 1) - A2 k) / (2 * Real.pi)), ?_⟩
  have hraw := sum_plaquette_raw A1 A2
  simp only [berryCurvature, redAngle_eq]
  rw [Finset.sum_sub_distrib, hraw, ← Finset.mul_sum]
  push_cast
  ring

/-- **TKNN (Thouless–Kohmoto–Nightingale–den Nijs).**

For any `U(1)` Berry connection on a discretized Brillouin torus, the Chern number of the
filled band is an integer, and the Hall conductance is exactly that integer times the
conductance quantum `e²/h`. -/
