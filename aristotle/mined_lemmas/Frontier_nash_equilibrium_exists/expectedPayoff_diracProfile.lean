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

theorem expectedPayoff_diracProfile (i : ι) (s : ∀ i, S i) :
    expectedPayoff g i (diracProfile s) = g i s := by
  unfold expectedPayoff
  rw [Finset.sum_congr rfl fun t _ => by rw [prod_diracProfile s t]]
  simp

