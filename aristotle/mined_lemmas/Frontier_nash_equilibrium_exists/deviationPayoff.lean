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

def deviationPayoff (g : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) (a : S i) : ℝ :=
  expectedPayoff g i (Function.update x i (pureStrat a))

/-- `x` is a mixed-strategy Nash equilibrium of the finite game with payoffs `g`:
it is a mixed profile, and no player can strictly improve their expected payoff by
unilaterally switching to another mixed strategy. -/
