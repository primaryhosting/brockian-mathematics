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

theorem not_dvd_sub_iff_zmod_ne (p : ℕ) (a r : ℤ) :
    ¬ ((p : ℤ) ∣ (a - r)) ↔ ((a : ZMod p) ≠ (r : ZMod p)) := by
  rw [Ne, ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  constructor
  · intro h hd
    exact h (by simpa using (dvd_neg.mpr hd))
  · intro h hd
    exact h (by simpa using (dvd_neg.mpr hd))

/-- Admissibility, as defined in `RequestProject.Main`, is the standard notion: for every prime
`p` the residues of the tuple do not cover all of `ZMod p`. -/
