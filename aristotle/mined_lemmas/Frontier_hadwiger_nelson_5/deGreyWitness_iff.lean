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

theorem deGreyWitness_iff : DeGreyWitness ↔ ¬ planeGraph.Colorable 4 := by
  refine ⟨plane_not_colorable_four, fun h => ?_⟩
  by_contra hw
  refine h (colorable_of_forall_finset planeGraph 4 ?_)
  unfold DeGreyWitness at hw
  push_neg at hw
  intro S
  obtain ⟨c, hc⟩ := hw S
  exact ⟨c, fun z hz w hw' hadj => hc z hz w hw' hadj⟩

/-- The chromatic number of the plane is at least `5` **iff** de Grey's finite witness
exists.  So the hypothesis of `hadwiger_nelson_5` is not merely sufficient but also
necessary; it is precisely the finite combinatorial content of the statement. -/
