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

def ComputesInTime (g : Word → Word) (f : ℕ → ℕ) : Prop :=
  ∀ x : Word, ∃ s ≤ f x.length,
    (M.run s (initConfig M.start x)).state = M.accept ∧
    (M.run s (initConfig M.start x)).head = 0 ∧
    (M.run s (initConfig M.start x)).tape = tapeOf (g x)

end DTM

/-! ## Nondeterministic machines -/

/-- A nondeterministic single-tape Turing machine with state set `Q`.  `step q a` is the set of
allowed transitions.  Acceptance is by reaching the state `accept`. -/
structure NTM (Q : Type) where
  /-- The initial state. -/
  start : Q
  /-- The accepting state. -/
  accept : Q
  /-- The transition relation: the set of allowed (new state, written symbol, movement) triples. -/
  step : Q → Alphabet → Set (Q × Alphabet × Dir)

namespace NTM

variable {Q : Type} (N : NTM Q)

/-- One computation step of a nondeterministic machine. -/
