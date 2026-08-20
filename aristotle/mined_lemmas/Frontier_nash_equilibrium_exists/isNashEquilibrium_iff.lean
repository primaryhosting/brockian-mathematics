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

theorem isNashEquilibrium_iff {x : ∀ i, S i → ℝ} (hx : x ∈ MixedProfiles S) :
    IsNashEquilibrium g x ↔ ∀ (i : ι) (a : S i), deviationPayoff g i x a ≤ expectedPayoff g i x := by
  constructor
  · rintro ⟨-, h⟩ i a
    exact h i (pureStrat a) (pureStrat_mem_stdSimplex a)
  · intro h
    refine ⟨hx, fun i y hy => ?_⟩
    rw [expectedPayoff_update]
    calc ∑ a : S i, y a * deviationPayoff g i x a
        ≤ ∑ a : S i, y a * expectedPayoff g i x := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (h i a) (hy.1 a)
      _ = expectedPayoff g i x := by rw [← Finset.sum_mul, hy.2, one_mul]

