/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

theorem determined_of_isOpenSeq {S : Set (ℕ → A)} (hS : IsOpenSeq S) : Determined S := by
  classical
  by_cases hI : IWins S []
  · obtain ⟨σ, hσ⟩ := hI
    exact Or.inl ⟨σ, hσ⟩
  · right
    refine ⟨fun p => if h : ∃ b, ¬ IWins S (p ++ [b]) then h.choose else default,
      fun x hx hxS => ?_⟩
    obtain ⟨-, hx2⟩ := hx
    have hgood : ∀ n, ¬ IWins S (hist x n) := by
      intro n
      induction n with
      | zero => simpa using hI
      | succ n ih =>
        rw [hist_succ]
        rcases Nat.even_or_odd n with he | ho
        · exact not_iWins_snoc_of_even (by simpa using he) ih (x n)
        · have hex : ∃ b, ¬ IWins S (hist x n ++ [b]) := exists_not_iWins_snoc ih
          have hxn := hx2 n (by simp) ho
          simp only [dif_pos hex] at hxn
          rw [hxn]
          exact hex.choose_spec
    obtain ⟨n, hn⟩ := hS x hxS
    refine hgood n (iWins_of_all_extensions (p := hist x n) fun y hy => hn y ?_)
    simpa using hy

/-- Clopen games are determined. -/
