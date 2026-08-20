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

def initConfig {Q : Type} (q : Q) (x : Word) : Config Q := ⟨q, 0, tapeOf x⟩

/-! ## Deterministic machines -/

/-- A deterministic single-tape Turing machine with state set `Q`.  The states `accept` and
`reject` are distinct halting states: the transition function fixes them (and leaves the tape
and the head alone), so that once the machine has accepted or rejected it stays there. -/
structure DTM (Q : Type) where
  /-- The initial state. -/
  start : Q
  /-- The accepting halting state. -/
  accept : Q
  /-- The rejecting halting state. -/
  reject : Q
  /-- The transition function: new state, symbol written, head movement. -/
  step : Q → Alphabet → Q × Alphabet × Dir
  /-- `accept` and `reject` really are different states. -/
  accept_ne_reject : accept ≠ reject
  /-- `accept` is a halting state. -/
  step_accept : ∀ a, step accept a = (accept, a, Dir.stay)
  /-- `reject` is a halting state. -/
  step_reject : ∀ a, step reject a = (reject, a, Dir.stay)

namespace DTM

variable {Q : Type} (M : DTM Q)

/-- One computation step of a deterministic machine. -/
