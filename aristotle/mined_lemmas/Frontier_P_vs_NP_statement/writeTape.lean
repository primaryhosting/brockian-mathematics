/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the formal statement of the P vs NP problem depends on as little as possible.

We define:
* single-tape deterministic Turing machines and their step-by-step semantics;
* single-tape nondeterministic Turing machines and their reachability semantics;
* the classes `Frontier.P` and `Frontier.NP` of languages decidable in polynomial time by
  deterministic resp. nondeterministic machines;
* polynomial-time computable functions, polynomial-time many-one reducibility `≤p`,
  NP-hardness and NP-completeness;
* the proposition `Frontier.PNeqNP`, i.e. `P ≠ NP`.

The main theorem `Frontier.P_vs_NP_statement` records the precise statement together with
its standard reformulation: `P ≠ NP` holds if and only if some language is decidable in
nondeterministic polynomial time but not in deterministic polynomial time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-! ## Words and languages -/

/-- Inputs are finite binary strings. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` a binary symbol. -/
abbrev Sym : Type := Option Bool

/-- A language is a set of binary strings, represented by its characteristic predicate. -/
abbrev Language : Type := Word → Prop

/-- Head movement directions. -/
inductive Dir : Type
  | left : Dir
  | right : Dir
  | stay : Dir
  deriving DecidableEq

/-- Moving the head position according to a direction. -/

def writeTape (tape : Int → Sym) (p : Int) (s : Sym) : Int → Sym :=
  fun i => if i = p then s else tape i

/-- A configuration of a machine with `n` states: current state, tape contents and head
position. -/
structure Cfg (n : Nat) : Type where
  q : Fin n
  tape : Int → Sym
  pos : Int

/-! ## Deterministic Turing machines -/

/-- A deterministic single-tape Turing machine with state set `Fin size`, a distinguished
start state, accepting state and rejecting state, and a transition function which, given
the current state and scanned symbol, returns the next state, the symbol to write and the
head movement. -/
structure TM : Type where
  size : Nat
  init : Fin size
  acc : Fin size
  rej : Fin size
  δ : Fin size → Sym → Fin size × Sym × Dir

/-- A configuration is halting if its state is the accepting or the rejecting state. -/
