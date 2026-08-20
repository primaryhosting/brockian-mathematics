import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open MeasureTheory

/-- The Brillouin zone, modelled as the unit square `[0,1] × [0,1]` in quasi-momentum
coordinates (the fundamental domain of the momentum-space torus). -/

def brillouinZone : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin zone:
the total Berry flux divided by `2π`. -/
