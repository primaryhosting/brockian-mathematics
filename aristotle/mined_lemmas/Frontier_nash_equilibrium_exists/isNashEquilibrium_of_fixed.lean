/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma isNashEquilibrium_of_fixed (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ}
    (hx : IsMixed x) (hfix : nashMap u x = x) : IsNashEquilibrium u x := by
  refine isNashEquilibrium_of_pure u hx fun i s => ?_
  have hden : (0 : ℝ) < 1 + ∑ t, gain u i t x := lt_of_lt_of_le zero_lt_one (one_le_denom u i x)
  have key : ∀ t : S i, x i t * (∑ r, gain u i r x) = gain u i t x := by
    intro t
    have h := congrFun (congrFun hfix i) t
    have h' : (x i t + gain u i t x) / (1 + ∑ r, gain u i r x) = x i t := h
    field_simp at h'
    linarith [h']
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_le u hx i
  have hg0 : gain u i s0 x = 0 := by
    simp only [gain]
    exact max_eq_left (by linarith)
  have hG : (∑ r, gain u i r x) = 0 := by
    have := key s0
    rw [hg0] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hs0pos.ne'
    · exact h
  have hgs : gain u i s x = 0 := by rw [← key s, hG, mul_zero]
  have : devPayoff u i s x - payoff u i x ≤ 0 := by
    have : max 0 (devPayoff u i s x - payoff u i x) = 0 := hgs
    exact max_eq_left_iff.mp this
  linarith

/-! ## Nash's theorem -/

/-- **Nash's theorem** (reduction to Brouwer's fixed point theorem): every finite game in
normal form, given by a finite set of players `ι`, finite nonempty pure strategy sets
`S i` and payoff functions `u i`, has a mixed strategy Nash equilibrium. -/
