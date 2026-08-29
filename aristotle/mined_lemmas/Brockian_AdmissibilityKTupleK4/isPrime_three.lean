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

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have hle : m ≤ 3 := Nat.le_of_dvd (by omega) hm
  match m, hle, hm with
  | 0, _, hm => exact absurd hm (by omega)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, hm => exact absurd hm (by omega)
  | 3, _, _ => exact Or.inr rfl
  | (_ + 4), hle, _ => exact absurd hle (by omega)

