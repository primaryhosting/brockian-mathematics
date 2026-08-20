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

theorem colPayoff_sub_const {A : M → N → ℝ} {p : M → ℝ} (hp : p ∈ stdSimplex ℝ M) (c : ℝ)
    (n : N) : colPayoff (fun m n => A m n - c) p n = colPayoff A p n - c := by
  simp only [colPayoff, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

