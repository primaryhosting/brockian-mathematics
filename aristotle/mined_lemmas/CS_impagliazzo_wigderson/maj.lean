/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

def maj {k : ℕ} (T : Bits k → Bool) : Bool := decide (1 / 2 < prob T)

/-- **Core derandomization step.**  If a generator `G` fools the test `T` to within `1/6`,
then the majority vote of `T ∘ G` over all seeds agrees with the bounded-error answer of `T`. -/
