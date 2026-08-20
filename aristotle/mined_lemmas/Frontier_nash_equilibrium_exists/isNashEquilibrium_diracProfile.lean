import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the very first command in a file, so the header comment
above is placed immediately after it.)
-/

open scoped BigOperators

namespace Frontier

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `a`, viewed as a (degenerate) mixed strategy. -/

theorem isNashEquilibrium_diracProfile {s : ∀ i, S i} (hs : IsPureNashEquilibrium g s) :
    IsNashEquilibrium g (diracProfile s) := by
  rw [isNashEquilibrium_iff (diracProfile_mem s)]
  intro i a
  rw [deviationPayoff_diracProfile, expectedPayoff_diracProfile]
  exact hs i a

/-- **Unconditional case: potential games.** A finite game admitting an exact potential has a
pure Nash equilibrium, namely any maximizer of the potential. -/
