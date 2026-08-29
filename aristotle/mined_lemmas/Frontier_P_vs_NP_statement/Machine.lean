import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Overview

We give a self-contained formalization of the classes `P` and `NP` in terms of
time-bounded (nondeterministic) Turing machines over the alphabet `Bool`, together with
polynomial-time many-one reducibility and NP-completeness.

The headline declaration `Frontier.P_vs_NP_statement` records the precise content of the
`P ≠ NP` question: the classes differ exactly when some language is verifiable in
nondeterministic polynomial time but not decidable in deterministic polynomial time.
(The nontrivial content of this equivalence is the inclusion `P ⊆ NP`, proved below as
`Frontier.P_subset_NP`.)  The truth value of `P ≠ NP` itself is, of course, open; what is
formalized and proved here is the statement together with all of its definitions.
-/

namespace Frontier

/-! ## Tapes and machines -/

/-- Head movements of a Turing machine. -/
inductive Move : Type
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- A two-way infinite tape: cells are indexed by `ℤ`, and `none` denotes a blank cell. -/
abbrev Tape : Type := ℤ → Option Bool

/-- A language is a set of finite binary strings. -/
abbrev Language : Type := Set (List Bool)

/-- A (possibly nondeterministic) Turing machine with state set `Q`.  The transition
relation `step q b q' b' m` says: in state `q`, reading `b`, the machine may move to state
`q'`, write `b'` on the current cell, and move the head according to `m`. -/
structure Machine (Q : Type) : Type where
  /-- The transition relation. -/
  step : Q → Option Bool → Q → Option Bool → Move → Prop
  /-- The initial state. -/
  start : Q
  /-- The accepting state. -/
  accept : Q

/-- A configuration: current state, head position and tape contents. -/
structure Config (Q : Type) : Type where
  /-- Current state. -/
  state : Q
  /-- Current head position. -/
  pos : ℤ
  /-- Current tape contents. -/
  tape : Tape

/-- Effect of a head movement on the head position. -/

def Machine.ComputesIn {Q : Type} (M : Machine Q) (x y : List Bool) (t : ℕ) : Prop :=
  ∃ n ≤ t, ∃ c : Config Q, M.reachesIn n (M.initConfig x) c ∧ c.state = M.accept ∧
    c.tape = initTape y

/-- `f : List Bool → List Bool` is computable in deterministic polynomial time. -/
