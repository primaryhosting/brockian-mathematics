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

theorem rowVal_le_bilin (M : A → B → ℝ) {x : A → ℝ} {y : B → ℝ}
    (hy : y ∈ stdSimplex ℝ B) : rowVal M x ≤ bilin M x y := by
  obtain ⟨hnn, hsum⟩ := hy
  rw [bilin_eq_sum_col]
  calc rowVal M x = ∑ b, y b * rowVal M x := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ b, y b * ∑ a, x a * M a b :=
        Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left
            (Finset.inf'_le (fun b => ∑ a, x a * M a b) (Finset.mem_univ b)) (hnn b)

omit [Nonempty B] [DecidableEq A] [DecidableEq B] in
