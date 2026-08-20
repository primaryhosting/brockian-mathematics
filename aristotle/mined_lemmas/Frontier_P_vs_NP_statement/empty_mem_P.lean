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

theorem empty_mem_P : (∅ : Language) ∈ P := by
  refine ⟨Bool, inferInstance, trivialDTM false, 0, 0, ?_⟩
  intro x
  refine ⟨⟨0, Nat.zero_le _, Or.inr ?_⟩, ?_⟩
  · rw [trivialDTM_run_state]; rfl
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, -, hs⟩
    rw [trivialDTM_run_state] at hs
    exact Bool.noConfusion hs

/-- The language of all words is in `NP`. -/
