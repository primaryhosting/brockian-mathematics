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

theorem prod_update (i : ι) (x : ∀ i, S i → ℝ) (y : S i → ℝ) (s : ∀ j, S j) :
    (∏ j, Function.update x i y j (s j))
      = y (s i) * ∏ j ∈ Finset.univ.erase i, x j (s j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The expected payoff is multilinear: as a function of player `i`'s mixed strategy it is
linear, so it is the corresponding convex combination of the pure deviation payoffs. -/
