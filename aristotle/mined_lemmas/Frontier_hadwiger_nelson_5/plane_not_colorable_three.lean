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

theorem plane_not_colorable_three : ¬ planeGraph.Colorable 3 := by
  rw [planeGraph_colorable_iff]
  rintro ⟨c, hc⟩
  obtain ⟨e01, e02, e12, e13, e23, e04, e05, e45, e46, e56, e36⟩ := spindle_edges
  rcases spindle_not_three_colorable (c (spindle 0)) (c (spindle 1)) (c (spindle 2))
      (c (spindle 3)) (c (spindle 4)) (c (spindle 5)) (c (spindle 6)) with
    h | h | h | h | h | h | h | h | h | h | h
  · exact hc _ _ e01 h
  · exact hc _ _ e02 h
  · exact hc _ _ e12 h
  · exact hc _ _ e13 h
  · exact hc _ _ e23 h
  · exact hc _ _ e04 h
  · exact hc _ _ e05 h
  · exact hc _ _ e45 h
  · exact hc _ _ e46 h
  · exact hc _ _ e56 h
  · exact hc _ _ e36 h

/-- **The chromatic number of the plane is at least `4`** (Nelson; the Moser spindle).
This is proved here unconditionally. -/
