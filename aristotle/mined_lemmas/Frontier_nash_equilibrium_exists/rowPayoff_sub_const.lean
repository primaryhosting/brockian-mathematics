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

theorem rowPayoff_sub_const {A : M → N → ℝ} {q : N → ℝ} (hq : q ∈ stdSimplex ℝ N) (c : ℝ)
    (m : M) : rowPayoff (fun m n => A m n - c) q m = rowPayoff A q m - c := by
  simp only [rowPayoff, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]

