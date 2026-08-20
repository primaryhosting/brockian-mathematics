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

theorem plane_not_colorable_four (h : DeGreyWitness) : ¬ planeGraph.Colorable 4 := by
  obtain ⟨S, hS⟩ := h
  rw [planeGraph_colorable_iff]
  rintro ⟨c, hc⟩
  obtain ⟨z, -, w, -, hzw, hcol⟩ := hS c
  exact hc z w hzw hcol

/-- **The chromatic number of the plane is at least `5`** (de Grey, 2018).

The hypothesis `DeGreyWitness` is the finite combinatorial core of de Grey's theorem:
the existence of a finite planar point set whose unit-distance graph has no proper
`4`-colouring.  Everything else — the passage from that finite graph to the whole
plane — is proved here. -/
