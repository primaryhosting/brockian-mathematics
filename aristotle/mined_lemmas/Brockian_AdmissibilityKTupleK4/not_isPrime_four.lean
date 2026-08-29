import Mathlib
import RequestProject.Main

/-!
# Admissibility of 4-tuples, `ZMod` formulation

Companion to `RequestProject.Main`.  The main file is developed without `import`s (its header
comment must be the very first thing in the file, which rules out importing Mathlib), so the
notions used there — primality and "the tuple avoids a residue class mod `p`" — are spelled out
from first principles.  Here we check, using Mathlib, that those notions agree with the
standard ones (`Nat.Prime` and non-surjectivity into `ZMod p`), and restate the main theorem
`Brockian.AdmissibilityKTupleK4` in that language.
-/

namespace Brockian

/-- The primality notion of `RequestProject.Main` is Mathlib's `Nat.Prime`. -/

theorem not_isPrime_four : ¬ IsPrime 4 := by
  intro hp
  cases hp.2 2 ⟨2, rfl⟩ with
  | inl h => exact absurd h (by omega)
  | inr h => exact absurd h (by omega)

/-- A prime other than `2` and `3` is at least `5`. -/
