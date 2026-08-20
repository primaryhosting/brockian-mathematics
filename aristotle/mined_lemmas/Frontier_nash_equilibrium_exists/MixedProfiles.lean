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

def MixedProfiles (S : ι → Type) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  {x | ∀ i, x i ∈ stdSimplex ℝ (S i)}

/-- The expected payoff of player `i` under the mixed profile `x`, for the game with
pure payoff functions `g`. -/
