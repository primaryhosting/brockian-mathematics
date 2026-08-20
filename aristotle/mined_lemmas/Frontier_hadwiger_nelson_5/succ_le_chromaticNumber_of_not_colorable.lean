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

lemma succ_le_chromaticNumber_of_not_colorable {n : ℕ} (h : ¬ planeGraph.Colorable n) :
    (n + 1 : ℕ∞) ≤ planeGraph.chromaticNumber := by
  by_contra hc
  push_neg at hc
  refine h (SimpleGraph.chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_succ ?_))
  rwa [Order.succ_eq_add_one]

/-! ## A convenient criterion for unit distance -/

/-- Two complex numbers are at distance `1` as soon as the sum of the squares of the
differences of their coordinates is `1`. -/
