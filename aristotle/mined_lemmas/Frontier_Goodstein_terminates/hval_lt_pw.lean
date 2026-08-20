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


theorem hval_lt_pw (h : HypSet α b pw mul) (hb : 2 ≤ b) {E m : ℕ} (hm : m < b ^ E) :
    hval b pw mul m < pw (hval b pw mul E) := (hval_key h hb E).2 m hm

end Generic

/-! ## The two instances: ordinals and natural numbers -/

/-- The ordinal obtained from the hereditary base-`b` representation of `n` by replacing
each occurrence of `b` by `ω`. -/
