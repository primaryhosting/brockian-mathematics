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

def ParisHarringtonAt (n k m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ, H ⊆ Finset.Icc 1 N ∧
    m ≤ H.card ∧ RelativelyLarge H ∧ ∃ i, Homog n c ↑H i

/-- The strengthened finite Ramsey theorem (Paris–Harrington principle). -/
