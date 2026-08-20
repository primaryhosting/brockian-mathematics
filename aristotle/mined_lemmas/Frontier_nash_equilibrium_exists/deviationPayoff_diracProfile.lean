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

theorem deviationPayoff_diracProfile (i : ι) (s : ∀ i, S i) (a : S i) :
    deviationPayoff g i (diracProfile s) a = g i (Function.update s i a) := by
  have h : Function.update (diracProfile s) i (pureStrat a)
      = diracProfile (Function.update s i a) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [diracProfile]
    · simp [diracProfile, Function.update_of_ne hj]
  rw [deviationPayoff, h, expectedPayoff_diracProfile]

/-- A pure Nash equilibrium gives a mixed Nash equilibrium. -/
