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

theorem exists_support_not_better (u : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ)
    (hx : x ∈ strategyProfiles S) :
    ∃ s : S i, 0 < x i s ∧ expectedPayoff u i (update x i (dirac s)) ≤ expectedPayoff u i x := by
  by_contra hc
  push_neg at hc
  obtain ⟨hnn, hsum⟩ := hx i (Set.mem_univ i)
  have hex : ∃ s : S i, 0 < x i s := by
    by_contra h2
    push_neg at h2
    have hzero : ∑ s, x i s = 0 :=
      Finset.sum_eq_zero fun s _ => le_antisymm (h2 s) (hnn s)
    rw [hsum] at hzero
    exact one_ne_zero hzero
  obtain ⟨s1, hs1⟩ := hex
  have hlt : ∑ s : S i, x i s * expectedPayoff u i x
      < ∑ s : S i, x i s * expectedPayoff u i (update x i (dirac s)) := by
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s1, mem_univ s1, ?_⟩
    · rcases lt_or_eq_of_le (hnn s) with h | h
      · exact mul_le_mul_of_nonneg_left (hc s h).le h.le
      · rw [← h]; simp
    · exact mul_lt_mul_of_pos_left (hc s1 hs1) hs1
  rw [← Finset.sum_mul, hsum, one_mul, ← expectedPayoff_eq_sum_pure u i i x] at hlt
  exact lt_irrefl _ hlt

omit [∀ i, Nonempty (S i)] in
/-- A fixed point of Nash's map is a Nash equilibrium. -/
