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

def IsNashEquilibrium (g : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : Prop :=
  x ∈ MixedProfiles S ∧
    ∀ i, ∀ y ∈ stdSimplex ℝ (S i),
      expectedPayoff g i (Function.update x i y) ≤ expectedPayoff g i x

/-- `s` is a pure-strategy Nash equilibrium: no player can improve by switching to
another pure strategy. -/
