/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Elementary facts about base-`b` digits -/


theorem bump_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (bump b) :=
  hval_strictMono (hypSet_nat b) hb

/-- Base change: the hereditary base-`(b+1)` value of `bump b n` is the hereditary base-`b`
value of `n`. -/
