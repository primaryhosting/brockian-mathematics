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

theorem expectedPayoff_update (i : ι) (x : ∀ i, S i → ℝ) (y : S i → ℝ) :
    expectedPayoff g i (Function.update x i y) = ∑ a : S i, y a * deviationPayoff g i x a := by
  have hL : expectedPayoff g i (Function.update x i y)
      = ∑ s : (∀ j, S j), y (s i) * ((∏ j ∈ Finset.univ.erase i, x j (s j)) * g i s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_update i x y s, mul_assoc]
  have hR : ∀ a : S i, deviationPayoff g i x a
      = ∑ s : (∀ j, S j),
          (if s i = a then (1 : ℝ) else 0) * ((∏ j ∈ Finset.univ.erase i, x j (s j)) * g i s) := by
    intro a
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_update i x (pureStrat a) s, mul_assoc]
    rfl
  rw [hL]
  simp_rw [hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

