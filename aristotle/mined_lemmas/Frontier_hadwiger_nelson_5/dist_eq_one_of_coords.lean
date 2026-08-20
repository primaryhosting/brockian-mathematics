import Mathlib

/-!
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` commands to appear before any other
command, and a module docstring `/-! ... -/` *is* a command.  The requested header
comment is therefore reproduced verbatim immediately after the single `import` line.
-/

namespace Frontier

open Real

/-! ## The unit-distance graph of the Euclidean plane

We model the Euclidean plane as `ℂ`, whose metric `dist z w = ‖z - w‖` is exactly the
Euclidean distance.  `planeGraph` is the unit-distance graph: two points are adjacent
iff they are at distance `1`.  Its chromatic number is the *chromatic number of the
plane*, the subject of the Hadwiger–Nelson problem.
-/

/-- The unit-distance graph on the Euclidean plane (modelled as `ℂ`). -/

lemma dist_eq_one_of_coords {z w : ℂ}
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1) : dist z w = 1 := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_one]

/-! ## The Moser spindle: the chromatic number of the plane is at least `4`

The seven points below are the vertices of the *Moser spindle*: two unit rhombi with a
common vertex at the origin, rotated against each other by the angle `θ` with
`cos θ = 5/6`, `sin θ = √11/6`, so that their far tips are again at distance `1`.
-/

/-- The seven vertices of the Moser spindle. -/
