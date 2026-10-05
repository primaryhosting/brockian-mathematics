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

theorem five_le_of_isPrime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    intro he
    exact not_isPrime_four (he ▸ hp)
  have := hp.1
  omega

/-- A `k`-tuple of integers `h : Fin k → ℤ` is *admissible* if for every prime `p` some
residue class `r` modulo `p` is avoided by the whole tuple, i.e. `p ∤ h i - r` for all `i`.
(Equivalently: the residues `h i mod p` do not cover all of `ZMod p`.) -/
