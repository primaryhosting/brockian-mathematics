/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Pigeonhole on five vertices two-coloured: three of them get the same colour. -/

lemma exists_three_same_color (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ f x = f y ∧ f y = f z := by
  revert f; decide

/-- Any 2-colouring of the edges of `K₆` contains a monochromatic triangle.  (Symmetry of `c`
is not needed here: the triangle produced is always oriented consistently, so the statement
holds for an arbitrary `Bool`-valued function on ordered pairs.) -/
