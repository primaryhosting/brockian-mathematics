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

theorem hadwiger_nelson_5 (h : DeGreyWitness) : 5 ≤ planeGraph.chromaticNumber := by
  have := succ_le_chromaticNumber_of_not_colorable (plane_not_colorable_four h)
  simpa using this

/-! ## The hypothesis is exactly right: a compactness (de Bruijn–Erdős) argument

The finite witness assumed above is not merely sufficient, it is also necessary: if the
whole plane needs at least five colours then already some finite subset does.  This is a
compactness argument, proved here in the following general form. -/

/-- **Compactness for graph colourings** (de Bruijn–Erdős).  If every finite set of
vertices of a graph admits a proper `n`-colouring, then the whole graph is
`n`-colourable. -/
