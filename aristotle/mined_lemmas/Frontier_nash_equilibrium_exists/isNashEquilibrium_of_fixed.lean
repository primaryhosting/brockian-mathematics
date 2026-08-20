import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the very first command in a file, so the header comment
above is placed immediately after it.)
-/

open scoped BigOperators

namespace Frontier

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `a`, viewed as a (degenerate) mixed strategy. -/

theorem isNashEquilibrium_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ MixedProfiles S)
    (hfix : nashMap g x = x) : IsNashEquilibrium g x := by
  rw [isNashEquilibrium_iff hx]
  intro i
  have hden : (0 : ℝ) < 1 + ∑ b : S i, gain g i x b := gain_denom_pos i x
  -- at a fixed point, each regret is proportional to the probability weight
  have key : ∀ a : S i, gain g i x a = x i a * ∑ b : S i, gain g i x b := by
    intro a
    have h := congrFun (congrFun hfix i) a
    simp only [nashMap] at h
    rw [div_eq_iff (ne_of_gt hden)] at h
    linear_combination h
  have hnn : ∀ a : S i, 0 ≤ x i a := (hx i).1
  have hsum1 : ∑ a : S i, x i a = 1 := (hx i).2
  -- some strategy in the support does no better than average
  have hstep : ∃ a : S i, x i a ≠ 0 ∧ deviationPayoff g i x a ≤ expectedPayoff g i x := by
    by_contra hcon
    push_neg at hcon
    have hv : expectedPayoff g i x = ∑ a : S i, x i a * deviationPayoff g i x a :=
      expectedPayoff_eq_sum i x
    obtain ⟨a₀, ha₀⟩ : ∃ a : S i, x i a ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_congr rfl fun a _ => h a] at hsum1
      simp at hsum1
    have hlt : ∑ a : S i, x i a * expectedPayoff g i x
        < ∑ a : S i, x i a * deviationPayoff g i x a := by
      refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
      · rcases eq_or_lt_of_le (hnn a) with h | h
        · simp [← h]
        · exact mul_le_mul_of_nonneg_left (hcon a (ne_of_gt h)).le h.le
      · exact mul_lt_mul_of_pos_left (hcon a₀ ha₀) (lt_of_le_of_ne (hnn a₀) (Ne.symm ha₀))
    rw [← Finset.sum_mul, hsum1, one_mul] at hlt
    exact absurd hv (ne_of_lt hlt)
  obtain ⟨a₀, hne, hle⟩ := hstep
  have hg0 : gain g i x a₀ = 0 := max_eq_left (by linarith)
  have hDzero : ∑ b : S i, gain g i x b = 0 := by
    have := key a₀
    rw [hg0] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hne
    · exact h
  intro a
  have h0 : gain g i x a = 0 := by rw [key a, hDzero, mul_zero]
  have hmax : deviationPayoff g i x a - expectedPayoff g i x ≤ gain g i x a := le_max_right _ _
  linarith

end NashMap

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- **Nash's theorem**: every finite game (finitely many players, each with a finite nonempty
set of pure strategies, and arbitrary real payoffs) has a mixed-strategy Nash equilibrium.

This is a Lean-checked reduction to Brouwer's fixed point theorem (hypothesis `hB`), which is
not available in Mathlib; everything else — Nash's map, its continuity, that it preserves the
product of simplices, and that its fixed points are exactly the equilibria — is proved here. -/
