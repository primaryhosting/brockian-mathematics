/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/

noncomputable def ramseyStep (c : ℕ → ℕ → Bool) (T : Set ℕ) : Set ℕ :=
  T ∩ Set.Ioi (pickElem T) ∩ {y | c (pickElem T) y = ufColor c (pickElem T)}

/-- The decreasing sequence of ultrafilter sets. -/
