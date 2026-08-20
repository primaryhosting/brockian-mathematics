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

def Step (c c' : Config Q) : Prop :=
  ∃ tr ∈ N.step c.state (c.tape c.head),
    c' = ⟨tr.1, tr.2.2.move c.head, writeAt c.tape c.head tr.2.1⟩

/-- `ReachesIn N t c c'` : the configuration `c'` is reachable from `c` in exactly `t` steps. -/
inductive ReachesIn : ℕ → Config Q → Config Q → Prop
  | refl (c : Config Q) : ReachesIn 0 c c
  | tail {t : ℕ} {c c' c'' : Config Q} :
      ReachesIn t c c' → N.Step c' c'' → ReachesIn (t + 1) c c''

/-- `N` accepts `x` within `t` steps: some computation path of length at most `t` starting from
the initial configuration reaches the accepting state. -/
