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

noncomputable def spindle : Fin 7 → ℂ :=
  ![ (⟨0, 0⟩ : ℂ),
     ⟨sqrt 3 / 2, 1 / 2⟩,
     ⟨sqrt 3 / 2, -(1 / 2)⟩,
     ⟨sqrt 3, 0⟩,
     ⟨(5 * sqrt 3 - sqrt 11) / 12, (sqrt 3 * sqrt 11 + 5) / 12⟩,
     ⟨(5 * sqrt 3 + sqrt 11) / 12, (sqrt 3 * sqrt 11 - 5) / 12⟩,
     ⟨5 * sqrt 3 / 6, sqrt 3 * sqrt 11 / 6⟩ ]

set_option maxHeartbeats 1000000 in
/-- The eleven edges of the Moser spindle really are unit distances. -/
