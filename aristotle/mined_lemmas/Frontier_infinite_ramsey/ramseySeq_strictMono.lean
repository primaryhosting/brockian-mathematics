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

lemma ramseySeq_strictMono (c : ℕ → ℕ → Bool) : StrictMono (ramseySeq c) :=
  fun _ _ h => ramseySeq_lt c h

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring
`c : ℕ → ℕ → Bool` of the unordered pairs of natural numbers (a pair `{x, y}` with
`x < y` receiving the colour `c x y`) there is an infinite set `S ⊆ ℕ` all of whose
pairs receive the same colour `b`. -/
