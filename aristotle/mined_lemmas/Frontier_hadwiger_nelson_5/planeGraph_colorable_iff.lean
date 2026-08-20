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

lemma planeGraph_colorable_iff (n : ℕ) :
    planeGraph.Colorable n ↔ ∃ c : ℂ → Fin n, ∀ z w : ℂ, dist z w = 1 → c z ≠ c w := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C, fun z w h => C.valid h⟩
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {z w} h => hc z w h⟩

/-- If the plane admits no proper `n`-colouring, its chromatic number is `> n`. -/
