import Mathlib

/-!
# The P vs NP statement

This file gives a self-contained formalization of the statement `P ≠ NP`, built from
scratch on top of a concrete Turing machine model:

* `Frontier.DTM`   : deterministic single-tape Turing machines over the alphabet `Option Bool`
                     (`none` is the blank symbol), with a finite state set;
* `Frontier.NTM`   : the nondeterministic variant;
* `Frontier.P`     : languages decided by a deterministic machine in polynomial time;
* `Frontier.NP`    : languages accepted by a nondeterministic machine in polynomial time;
* `Frontier.PolyTimeComputable`, `Frontier.PolyReducible` (`≤p`) : polynomial-time computable
  functions and polynomial-time many-one reducibility, together with `Frontier.NPHard` and
  `Frontier.NPComplete`;
* `Frontier.P_vs_NP_statement` : the proposition `P ≠ NP`.

`P_vs_NP_statement` is the famous open problem, so it is *stated*, not proved here.  What is
proved here are the basic structural facts that make the statement meaningful: `P ⊆ NP`,
the fact that `P ≠ NP` is equivalent to the existence of a language in `NP \ P`,
reflexivity of `≤p`, and the fact that the trivial languages are in `P` (so the definitions
are not vacuous).
-/

namespace Frontier

/-! ## Words, languages, tapes -/

/-- Words are finite binary strings. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

/-- The tape alphabet: `none` is the blank symbol. -/
abbrev Alphabet := Option Bool

/-- A tape is a bi-infinite sequence of tape symbols. -/
abbrev Tape := ℤ → Alphabet

/-- Directions the head can move in one step. -/
inductive Dir
  | left
  | right
  | stay
  deriving DecidableEq, Fintype

/-- Moving a head position in a given direction. -/

theorem compl_mem_P {L : Language} (hL : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨Q, hQ, M, c, k, hM⟩ := hL
  refine ⟨Q, hQ, M.swap, c, k, ?_⟩
  intro x
  obtain ⟨⟨s, hs, hstate⟩, hiff⟩ := hM x
  have hrun : ∀ t : ℕ, (M.swap.run t (initConfig M.swap.start x))
      = M.run t (initConfig M.start x) := fun _ => rfl
  refine ⟨⟨s, hs, hstate.symm⟩, ?_⟩
  simp only [DTM.AcceptsIn, hrun, Set.mem_compl_iff]
  constructor
  · rintro ⟨s₁, hs₁, hrej⟩ hxL
    obtain ⟨s₂, hs₂, hacc⟩ := hiff.2 hxL
    have h₁ : (M.run (max s₁ s₂) (initConfig M.start x)).state = M.reject :=
      M.run_state_persist M.step_reject (le_max_left _ _) hrej
    have h₂ : (M.run (max s₁ s₂) (initConfig M.start x)).state = M.accept :=
      M.run_state_persist M.step_accept (le_max_right _ _) hacc
    exact M.accept_ne_reject (h₂ ▸ h₁)
  · intro hxL
    rcases hstate with hacc | hrej
    · exact absurd (hiff.1 ⟨s, hs, hacc⟩) hxL
    · exact ⟨s, hs, hrej⟩

/-! ## The definitions are not vacuous -/

/-- A two-state machine that never moves and never changes the tape; `q = true` is the accepting
state and `q = false` the rejecting one, and `b` is chosen as the starting state. -/
