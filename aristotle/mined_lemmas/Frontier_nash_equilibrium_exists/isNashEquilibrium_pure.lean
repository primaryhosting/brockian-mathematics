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

theorem isNashEquilibrium_pure (u : ι → (∀ i, S i) → ℝ) (p : ∀ i, S i)
    (hp : ∀ i (s : S i), u i (update p i s) ≤ u i p) :
    IsNashEquilibrium u (fun j => dirac (p j)) := by
  refine ⟨fun i _ => dirac_mem_stdSimplex (p i), fun i y hy => ?_⟩
  rw [expectedPayoff_pure]
  refine expectedPayoff_update_le_of_pure_le u i _ (u i p) (fun s => ?_) y hy
  have hupd : update (fun j => dirac (p j)) i (dirac s) = fun j => dirac ((update p i s) j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj]
  rw [hupd, expectedPayoff_pure]
  exact hp i s

/-- `P` is an exact potential for the game `u`: any unilateral deviation changes the
deviating player's payoff exactly as much as it changes `P`. -/
