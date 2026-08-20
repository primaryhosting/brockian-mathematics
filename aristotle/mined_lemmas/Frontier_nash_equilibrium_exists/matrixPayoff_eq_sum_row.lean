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

theorem matrixPayoff_eq_sum_row (A : M → N → ℝ) (p : M → ℝ) (q : N → ℝ) :
    matrixPayoff A p q = ∑ m, p m * rowPayoff A q m := by
  simp only [matrixPayoff, rowPayoff, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring

