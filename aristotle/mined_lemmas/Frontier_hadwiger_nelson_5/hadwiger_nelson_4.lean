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

theorem hadwiger_nelson_4 : 4 ≤ planeGraph.chromaticNumber := by
  have := succ_le_chromaticNumber_of_not_colorable plane_not_colorable_three
  simpa using this

/-! ## The chromatic number of the plane is at least `5`

De Grey (2018) exhibited an explicit *finite* set of points of the plane whose
unit-distance graph is not `4`-colourable (his graph has `1581` vertices; smaller
examples are now known).  That finite, computational statement is isolated below as
`DeGreyWitness`.
-/

/-- **De Grey's finite witness.**  There is a finite set of points of the Euclidean plane
whose unit-distance graph admits no proper `4`-colouring.

This is the (purely finite, computer-verified) combinatorial input of de Grey's 2018
theorem; it is *not* proved here. -/
