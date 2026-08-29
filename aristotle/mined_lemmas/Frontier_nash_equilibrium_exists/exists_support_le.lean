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

lemma exists_support_le (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ} (hx : IsMixed x)
    (i : ι) : ∃ s : S i, 0 < x i s ∧ devPayoff u i s x ≤ payoff u i x := by
  classical
  set T : Finset (S i) := univ.filter (fun s => 0 < x i s) with hT
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ s : S i, x i s = 0 := by
      intro s
      rcases lt_or_eq_of_le ((hx i).1 s) with hlt | heq
      · exact absurd (Finset.mem_filter.mpr ⟨mem_univ s, hlt⟩) (by rw [← hT, h]; simp)
      · exact heq.symm
    have := (hx i).2
    rw [Finset.sum_congr rfl fun s _ => hzero s] at this
    simp at this
  obtain ⟨s0, hs0T, hs0min⟩ := T.exists_min_image (fun s => devPayoff u i s x) hTne
  have hs0pos : 0 < x i s0 := (Finset.mem_filter.mp hs0T).2
  refine ⟨s0, hs0pos, ?_⟩
  have hle : ∑ s, x i s * devPayoff u i s0 x ≤ ∑ s, x i s * devPayoff u i s x := by
    refine Finset.sum_le_sum fun s _ => ?_
    rcases lt_or_eq_of_le ((hx i).1 s) with hlt | heq
    · exact mul_le_mul_of_nonneg_left
        (hs0min s (Finset.mem_filter.mpr ⟨mem_univ s, hlt⟩)) hlt.le
    · rw [← heq]; simp
  rw [← Finset.sum_mul, (hx i).2, one_mul] at hle
  rw [payoff_eq_sum]
  exact hle

/-- A fixed point of Nash's map is a Nash equilibrium. -/
