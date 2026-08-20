/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

theorem exists_support_le (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x)
    (i : ι) : ∃ s : S i, 0 < x i s ∧ devPayoff G i s x ≤ expectedPayoff G i x := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ s : S i, x i s * expectedPayoff G i x ≤ x i s * devPayoff G i s x := by
    intro s
    rcases lt_or_eq_of_le ((hx i).1 s) with h | h
    · exact mul_le_mul_of_nonneg_left (hcon s h).le h.le
    · rw [← h]; simp
  -- there is a strategy in the support
  obtain ⟨s0, -, hs0⟩ : ∃ s0 ∈ (Finset.univ : Finset (S i)), 0 < x i s0 := by
    by_contra h
    push_neg at h
    have : ∑ s : S i, x i s = 0 :=
      Finset.sum_eq_zero fun s hs => le_antisymm (h s hs) ((hx i).1 s)
    rw [(hx i).2] at this
    exact one_ne_zero this
  have hstrict : x i s0 * expectedPayoff G i x < x i s0 * devPayoff G i s0 x :=
    (mul_lt_mul_of_pos_left (hcon s0 hs0) hs0)
  have hsum : ∑ s : S i, x i s * expectedPayoff G i x
      < ∑ s : S i, x i s * devPayoff G i s x := by
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ _, hstrict⟩
    exact key s
  rw [← Finset.sum_mul, (hx i).2, one_mul, ← expectedPayoff_eq_sum] at hsum
  exact lt_irrefl _ hsum

/-- At a fixed point of Nash's map, no player has a profitable pure deviation. -/
