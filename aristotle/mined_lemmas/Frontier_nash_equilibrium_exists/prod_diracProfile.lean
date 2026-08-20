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

theorem prod_diracProfile (s t : ∀ i, S i) :
    (∏ j, diracProfile s j (t j)) = if t = s then (1 : ℝ) else 0 := by
  by_cases h : t = s
  · subst h
    simp [diracProfile, pureStrat]
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, t j ≠ s j := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp [diracProfile, pureStrat, hj]

