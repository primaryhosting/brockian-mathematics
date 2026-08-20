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

theorem nonempty_mixedProfiles [∀ i, Nonempty (S i)] : (MixedProfiles S).Nonempty :=
  ⟨fun i => pureStrat (Classical.arbitrary (S i)), fun i => pureStrat_mem_stdSimplex _⟩

end Basic

section NashMap

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The regret of player `i` at `x` for the pure strategy `a`: the (nonnegative part of the)
gain from deviating to `a`. -/
