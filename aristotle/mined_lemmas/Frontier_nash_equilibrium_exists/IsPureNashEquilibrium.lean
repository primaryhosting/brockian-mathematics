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

def IsPureNashEquilibrium (g : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ (i : ι) (a : S i), g i (Function.update s i a) ≤ g i s

/-- `P` is an exact potential for the game `g` (Monderer–Shapley): every unilateral
deviation changes the deviating player's payoff exactly as it changes `P`. -/
