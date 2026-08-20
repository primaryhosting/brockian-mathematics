/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file gives a precise, self-contained formalization of the statement
`P ≠ NP`, in terms of time-bounded (deterministic and nondeterministic)
one-tape Turing machines, together with polynomial-time many-one reducibility
and NP-completeness.

The file deliberately uses no imports beyond Lean's `Init`, so that the meaning
of the statement depends on nothing but the definitions given here.

The main theorem `Frontier.P_vs_NP_statement` records the equivalence between
the assertion `P ≠ NP` and the existence of a language lying in `NP` but not in
`P`.  (Whether that assertion is *true* is the open Millennium Problem; what is
proved here is the equivalence of the two formulations, which rests on the
inclusion `P ⊆ NP`, proved below as `Frontier.P_subset_NP`.)
-/

namespace Frontier

/-! ## Machine model

A one-tape Turing machine over the binary alphabet.  The tape is bi-infinite,
indexed by `ℤ`; a cell holds `some b` for a bit `b`, or `none` for the blank.
Nondeterminism is part of the model: the transition relation `next q a` may
relate a (state, scanned symbol) pair to any number of successor triples
(new state, symbol written, head move).  A machine is *deterministic* when each
such set of successors has at most one element.
-/

/-- A head move: left, stay, or right. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- The displacement of the head associated with a move. -/

def P_ne_NP : Prop := P ≠ NP

/-- **The P versus NP statement.**

With `P` and `NP` defined through time-bounded (deterministic, respectively
nondeterministic) one-tape Turing machines as above, the assertion `P ≠ NP` is
equivalent to the existence of a language that is decidable by a
polynomial-time nondeterministic machine but by no polynomial-time
deterministic machine.

Whether the assertion holds is the open Millennium Problem; what is proved here
is the equivalence of the two formulations, which rests on the inclusion
`P ⊆ NP` (`Frontier.P_subset_NP`). -/
