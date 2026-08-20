/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

lemma exists_play (σ τ : List X → X) :
    ∃ a : ℕ → X, FollowsI σ a ∧ FollowsII τ a := by
  refine ⟨playSeq σ τ, ?_, ?_⟩
  · intro n hn
    rw [hist_playSeq]
    simp [playSeq, hn]
  · intro n hn
    rw [hist_playSeq]
    have : ¬ Even n := Nat.not_even_iff_odd.mpr hn
    simp [playSeq, this]

end Strategies

section Win

/-- The (data-valued) derivation that player I can force reaching `W` from position `p`. -/
inductive WinT (W : Set (List X)) : List X → Type u
  | base {p : List X} : p ∈ W → WinT W p
  | moveI {p : List X} (x : X) : Even p.length → WinT W (p ++ [x]) → WinT W p
  | moveII {p : List X} : Odd p.length → (∀ x : X, WinT W (p ++ [x])) → WinT W p

end Win

variable [Nonempty X]

/-- From a derivation that I can force `W` from `p`, one extracts a strategy for I. -/
