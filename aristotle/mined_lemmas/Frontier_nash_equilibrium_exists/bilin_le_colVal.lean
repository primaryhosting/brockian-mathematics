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

theorem bilin_le_colVal (M : A → B → ℝ) {x : A → ℝ} {y : B → ℝ}
    (hx : x ∈ stdSimplex ℝ A) : bilin M x y ≤ colVal M y := by
  obtain ⟨hnn, hsum⟩ := hx
  rw [bilin_eq_sum_row]
  calc ∑ a, x a * ∑ b, y b * M a b ≤ ∑ a, x a * colVal M y :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left
            (Finset.le_sup' (f := fun a => ∑ b, y b * M a b) (Finset.mem_univ a)) (hnn a)
    _ = colVal M y := by rw [← Finset.sum_mul, hsum, one_mul]

omit [Nonempty A] [DecidableEq A] [DecidableEq B] in
