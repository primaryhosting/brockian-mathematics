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

variable {A : Type u}

/-! ## The game framework

We consider infinite two–player games on a set `A` of moves.  A *play* is a sequence
`x : ℕ → A`; player `0` chooses the moves `x n` with `n` even, player `1` chooses the moves
`x n` with `n` odd.  A *strategy* is a function `List A → A` assigning a move to every finite
position (the player only consults it at their own turns). -/

/-- The length-`n` initial segment of a play. -/

theorem gale_stewart (i : ℕ) {S : Set (ℕ → A)} (hS : IsClosed S) :
    (∃ s, WinsFor i S s) ∨ (∃ s, WinsFor (i + 1) Sᶜ s) := by
  classical
  set T : List A → Prop := fun p => ∃ y ∈ S, pre y p.length = p
  have hTS : ∀ x : ℕ → A, (∀ n, T (pre x n)) → x ∈ S := by
    intro x hx
    by_contra hxS
    obtain ⟨n, hn⟩ := exists_pre_of_notMem hS hxS
    obtain ⟨y, hyS, hy⟩ := hx n
    rw [pre_length] at hy
    exact hn y hy hyS
  by_cases h : OppWins i T []
  · right
    obtain ⟨s, hs⟩ := exists_strategy_of_oppWins i T h
    refine ⟨s, fun x hxf hxS => ?_⟩
    obtain ⟨n, hn⟩ : ∃ n, ¬ T (pre x n) := by
      refine hs x (by simp) (fun n _ hpar => hxf n ?_)
      rw [parity_succ]
      exact hpar
    exact hn ⟨x, hxS, by rw [pre_length]⟩
  · left
    obtain ⟨s, hs⟩ := exists_strategy_of_not_oppWins i T h
    exact ⟨s, fun x hx => hTS x (hs x hx)⟩

end GaleStewart

/-! ## The Borel hierarchy -/

section Borel

variable [TopologicalSpace A]

/-- `S` is a Borel subset of the space of plays `ℕ → A` (product topology, `A` discrete). -/
