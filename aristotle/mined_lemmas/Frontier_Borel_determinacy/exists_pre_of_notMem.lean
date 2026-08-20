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

lemma exists_pre_of_notMem {S : Set (ℕ → A)} (hS : IsClosed S) {x : ℕ → A} (hx : x ∉ S) :
    ∃ n, ∀ y : ℕ → A, pre y n = pre x n → y ∉ S := by
  have hmem : Sᶜ ∈ nhds x := hS.isOpen_compl.mem_nhds hx
  rw [nhds_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := Filter.mem_pi.1 hmem
  obtain ⟨n, hn⟩ : ∃ n, ∀ i ∈ I, i < n := by
    obtain ⟨n, hn⟩ := hI.bddAbove
    exact ⟨n + 1, fun i hi => lt_of_le_of_lt (hn hi) (lt_add_one n)⟩
  refine ⟨n, fun y hy hyS => ?_⟩
  refine hsub (fun i hi => ?_) hyS
  have hxi : x i ∈ t i := mem_nhds_discrete.1 (ht i)
  have : y i = x i := eq_of_pre_eq hy (hn i hi)
  rw [this]
  exact hxi

/-- **Gale–Stewart theorem**: a game with closed payoff set is determined, for either
assignment of the roles to the two players (`i` is the player aiming at the closed set `S`). -/
