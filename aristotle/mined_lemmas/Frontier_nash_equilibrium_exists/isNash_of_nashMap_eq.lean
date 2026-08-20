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

theorem isNash_of_nashMap_eq (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ}
    (hx : IsMixed x) (hfix : nashMap G x = x) : IsNash G x := by
  rw [isNash_iff G hx]
  intro i
  -- the total regret of player `i` vanishes
  have hpos := one_add_sum_gain_pos G i x
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_le G hx i
  have hg0 : gain G i s0 x = 0 := by
    simp only [gain, max_eq_left_iff]
    linarith
  have hfix0 : (x i s0 + gain G i s0 x) / (1 + ∑ t : S i, gain G i t x) = x i s0 := by
    have := congrFun (congrFun hfix i) s0
    simpa [nashMap] using this
  rw [hg0, add_zero, div_eq_iff (ne_of_gt hpos)] at hfix0
  have hG : ∑ t : S i, gain G i t x = 0 := by
    have : x i s0 * (∑ t : S i, gain G i t x) = 0 := by nlinarith [hfix0]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt hs0pos)
    · exact h
  intro s
  have hzero : gain G i s x = 0 :=
    le_antisymm
      (by
        have := Finset.single_le_sum (f := fun t : S i => gain G i t x)
          (fun t _ => gain_nonneg G i t x) (Finset.mem_univ s)
        rw [hG] at this
        exact this)
      (gain_nonneg G i s x)
  have : devPayoff G i s x - expectedPayoff G i x ≤ 0 := by
    by_contra h
    push_neg at h
    rw [gain, max_eq_right h.le] at hzero
    linarith
  linarith

/-! ### The main theorem -/

/-- **Nash's theorem** (reduced to Brouwer's fixed point theorem): every finite game
in which every player has at least one strategy has a mixed strategy Nash equilibrium. -/
