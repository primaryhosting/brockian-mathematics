import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem expectedPayoff_update_le_of_pure_le (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (x : ∀ i, S i → ℝ) (c : ℝ) (h : ∀ s : S i, expectedPayoff u i (update x i (dirac s)) ≤ c)
    (y : S i → ℝ) (hy : y ∈ stdSimplex ℝ (S i)) :
    expectedPayoff u i (update x i y) ≤ c := by
  obtain ⟨hnn, hsum⟩ := hy
  rw [expectedPayoff_eq_sum_pure u i i (update x i y)]
  calc ∑ s : S i, (update x i y) i s * expectedPayoff u i (update (update x i y) i (dirac s))
      = ∑ s : S i, y s * expectedPayoff u i (update x i (dirac s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [update_idem, update_self]
    _ ≤ ∑ s : S i, y s * c := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hnn s)
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

omit [∀ i, Nonempty (S i)] in
/-- The expected payoff at a pure profile is the payoff of that profile. -/
