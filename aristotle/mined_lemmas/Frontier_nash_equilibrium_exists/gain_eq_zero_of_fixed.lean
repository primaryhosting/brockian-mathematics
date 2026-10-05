/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Set Function

namespace Frontier

/-! ## Finite games in normal form

A finite game in normal form consists of a finite set of players `I`, for each player a finite
nonempty set of pure strategies `S i`, and a payoff function `u i : (∀ j, S j) → ℝ`.

A *mixed strategy* for player `i` is an element of `stdSimplex ℝ (S i)`, and a *mixed strategy
profile* is an element of the product of these simplices. -/

section Game

variable {I : Type} [Fintype I] [DecidableEq I]
  (S : I → Type) [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  (u : I → (∀ i, S i) → ℝ)

/-- The set of mixed strategy profiles of a finite game. -/

theorem gain_eq_zero_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ profiles S)
    (hfix : nashMap u x = x) (i : I) (s : S i) : gain u x i s = 0 := by
  have hxi := hx i (Set.mem_univ i)
  set D : ℝ := ∑ t : S i, gain u x i t with hD
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun t _ => gain_nonneg u x i t
  have hpos : (0 : ℝ) < 1 + D := gain_denom_pos u x i
  -- the fixed point equation, rearranged
  have key : ∀ t : S i, gain u x i t = x i t * D := by
    intro t
    have h := congrFun (congrFun hfix i) t
    rw [nashMap, div_eq_iff (ne_of_gt hpos)] at h
    nlinarith [h]
  -- if the total gain were positive, some strategy in the support would be a strict
  -- improvement over the equilibrium payoff, which is impossible
  have hD0 : D = 0 := by
    by_contra hne
    have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hne)
    set V := expectedPayoff S u x i with hV
    set A : S i → ℝ := fun t => expectedPayoff S u (Function.update x i (Pi.single t 1)) i
      with hA
    have hsum : V = ∑ t : S i, x i t * A t := expectedPayoff_eq_sum u x i i
    -- there is a strategy in the support of `x i` which is not strictly better than `V`
    have hex : ∃ t : S i, 0 < x i t ∧ A t ≤ V := by
      by_contra hcon
      push_neg at hcon
      have hlt : ∑ t : S i, x i t * V < ∑ t : S i, x i t * A t := by
        refine Finset.sum_lt_sum (fun t _ => ?_) ?_
        · rcases eq_or_lt_of_le (hxi.1 t) with h | h
          · simp [← h]
          · exact le_of_lt (by have := hcon t h; nlinarith)
        · -- some strategy has positive weight, since the weights sum to `1`
          obtain ⟨t, -, ht⟩ : ∃ t ∈ Finset.univ, 0 < x i t := by
            by_contra hall
            push_neg at hall
            have : ∑ t : S i, x i t = 0 :=
              Finset.sum_eq_zero fun t ht => le_antisymm (hall t ht) (hxi.1 t)
            rw [hxi.2] at this; exact one_ne_zero this
          exact ⟨t, Finset.mem_univ t, by have := hcon t ht; nlinarith⟩
      rw [← Finset.sum_mul, hxi.2, one_mul, ← hsum] at hlt
      exact lt_irrefl V hlt
    obtain ⟨t, ht, hAt⟩ := hex
    have hAt' : expectedPayoff S u (Function.update x i (Pi.single t 1)) i
        ≤ expectedPayoff S u x i := hAt
    have hzero : gain u x i t = 0 := max_eq_left (by linarith)
    rw [key t] at hzero
    nlinarith
  rw [key s, hD0, mul_zero]

/-- A fixed point of Nash's map inside the set of profiles is a Nash equilibrium. -/
