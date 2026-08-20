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

theorem colPayoff_pureStrat (A : M → N → ℝ) (m : M) (n : N) :
    colPayoff A (fun m' => if m = m' then 1 else 0) n = A m n := by
  simp [colPayoff]

/-- **Ville's theorem of the alternative.** For any real matrix `A`, either the row player has
a mixed strategy guaranteeing a nonnegative payoff against every column, or the column player
has a mixed strategy guaranteeing a strictly negative payoff against every row. -/
