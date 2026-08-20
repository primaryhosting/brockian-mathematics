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

lemma spindle_edges :
    dist (spindle 0) (spindle 1) = 1 ∧ dist (spindle 0) (spindle 2) = 1 ∧
    dist (spindle 1) (spindle 2) = 1 ∧ dist (spindle 1) (spindle 3) = 1 ∧
    dist (spindle 2) (spindle 3) = 1 ∧ dist (spindle 0) (spindle 4) = 1 ∧
    dist (spindle 0) (spindle 5) = 1 ∧ dist (spindle 4) (spindle 5) = 1 ∧
    dist (spindle 4) (spindle 6) = 1 ∧ dist (spindle 5) (spindle 6) = 1 ∧
    dist (spindle 3) (spindle 6) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h33 : (Real.sqrt 3 * Real.sqrt 11) ^ 2 = 33 := by rw [mul_pow, h3, h11]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply dist_eq_one_of_coords
     simp only [spindle, Matrix.cons_val]
     nlinarith [h3, h11, h33])

/-- The abstract Moser spindle is not `3`-colourable. -/
