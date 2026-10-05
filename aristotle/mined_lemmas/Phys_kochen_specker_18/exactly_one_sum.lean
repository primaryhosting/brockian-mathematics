/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
given with integer coordinates. -/

private lemma exactly_one_sum (p : Fin 4 → Bool) (j : Fin 4) (hj : p j = true)
    (hu : ∀ y : Fin 4, p y = true → y = j) :
    (cond (p 0) 1 0) + (cond (p 1) 1 0) + (cond (p 2) 1 0) + (cond (p 3) 1 0) = (1 : ℕ) := by
  revert hj hu
  revert j
  revert p
  decide

/--
**Kochen–Specker theorem (18-vector version).**
The explicit set of 18 vectors in `ℝ⁴` above, grouped into nine orthogonal bases,
admits no `{0,1}`-coloring assigning to each vector a value in `{false, true}`
such that each of the nine bases contains exactly one vector coloured `true`.
-/
