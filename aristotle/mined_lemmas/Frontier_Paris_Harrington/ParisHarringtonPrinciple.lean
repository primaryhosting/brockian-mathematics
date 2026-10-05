import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Set

/-- `Homog n c T i` says: every `n`-element subset of the set `T` gets colour `i` under `c`. -/

def ParisHarringtonPrinciple : Prop := ∀ n k m : ℕ, ParisHarringtonAt n k m

/-- The infinite Ramsey theorem, relativised to an arbitrary infinite set of naturals. -/
