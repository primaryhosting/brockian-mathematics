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

theorem expectedPayoff_eq_sum_pure (u : ι → (∀ i, S i) → ℝ) (i k : ι) (x : ∀ i, S i → ℝ) :
    expectedPayoff u k x = ∑ s : S i, x i s * expectedPayoff u k (update x i (dirac s)) := by
  set F : (∀ j, S j) → ℝ := fun p => ∏ j ∈ univ.erase i, x j (p j)
  have h1 : ∀ p : ∀ j, S j, ∏ j, x j (p j) = x i (p i) * F p := fun p =>
    (Finset.mul_prod_erase univ (fun j => x j (p j)) (mem_univ i)).symm
  have h2 : ∀ (s : S i) (p : ∀ j, S j),
      ∏ j, (update x i (dirac s)) j (p j) = dirac s (p i) * F p := by
    intro s p
    rw [← Finset.mul_prod_erase univ (fun j => (update x i (dirac s)) j (p j)) (mem_univ i),
      update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  have key : ∀ p : ∀ j, S j, ∑ s : S i, x i s * dirac s (p i) = x i (p i) := by
    intro p
    simp [dirac, Finset.sum_ite_eq]
  calc expectedPayoff u k x = ∑ p : ∀ j, S j, x i (p i) * (F p * u k p) := by
        simp only [expectedPayoff, h1, mul_assoc]
    _ = ∑ p : ∀ j, S j, ∑ s : S i, x i s * (dirac s (p i) * (F p * u k p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← key p, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = ∑ s : S i, ∑ p : ∀ j, S j, x i s * (dirac s (p i) * (F p * u k p)) := Finset.sum_comm
    _ = ∑ s : S i, x i s * expectedPayoff u k (update x i (dirac s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [expectedPayoff, h2, Finset.mul_sum, mul_assoc]

omit [∀ i, Nonempty (S i)] in
/-- If no pure deviation of player `i` beats the value `c`, then no mixed deviation does. -/
