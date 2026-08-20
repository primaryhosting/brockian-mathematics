import RequestProject.Main

/-!
# A concrete model: the Fock space of finitely supported sequences

This file constructs an explicit `QPhys.LadderSystem`, showing that the hypotheses of
`QPhys.oscillator_spectrum` are consistent (non-vacuous).

The state space is `ℕ →₀ ℂ`, the space of finitely supported complex sequences,
with the usual `ℓ²` inner product `⟪f, g⟫ = ∑ conj (f i) * g i`.  The basis vector
`|n⟩ = single n 1` plays the role of the `n`-th excited state, and the ladder operators
act by `a |n⟩ = √n |n-1⟩`, `a† |n⟩ = √(n+1) |n+1⟩`.
-/

open scoped InnerProductSpace

namespace QPhys

namespace Fock

/-- The `ℓ²` inner product on finitely supported complex sequences. -/

lemma numberOp_eigenvalue_nat_of_le :
    ∀ (k : ℕ) (r : ℝ) (x : H), x ≠ 0 → numberOp L x = ((r : ℝ) : ℂ) • x → r ≤ k →
      ∃ m : ℕ, r = (m : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro r x hx hE hr
      have h0 : ((r : ℝ) : ℂ) = ((‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) :=
        numberOp_eigenvalue_real L hx hE
      have hr0 : r = ‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 := by exact_mod_cast h0
      have hnn : 0 ≤ r := by rw [hr0]; positivity
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero] at hr ⊢
      linarith
  | succ k ih =>
      intro r x hx hE hr
      by_cases hax : L.lower x = 0
      · have hz : ((r : ℝ) : ℂ) • x = 0 := by
          rw [← hE, numberOp_apply, hax, map_zero]
        rcases smul_eq_zero.mp hz with h | h
        · exact ⟨0, by exact_mod_cast h⟩
        · exact absurd h hx
      · obtain ⟨m, hm⟩ := ih (r - 1) (L.lower x) hax (numberOp_eigen_lower L hE)
          (by push_cast at hr ⊢; linarith)
        exact ⟨m + 1, by push_cast; linarith⟩

/-- Every eigenvalue of the number operator is a natural number. -/
