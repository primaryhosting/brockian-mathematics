/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file gives a self-contained formalization of the complexity classes `P` and `NP` in
terms of time-bounded (deterministic and nondeterministic) single-tape Turing machines
over the binary alphabet, together with polynomial-time many-one reducibility `≤p`.

Mathlib provides Turing machine models (`Turing.TM0`, `Turing.TM1`, `Turing.TM2`, …) but
no notion of *time-bounded* computation and no complexity classes, so the model below is
developed from scratch; no Mathlib lemma comes close to settling `P = NP`, which is of
course open.  (The file uses only Lean core, so that the required header comment can be
the very first thing in it.)

The open problem itself is recorded as the proposition `Frontier.PNeqNP := P ≠ NP`, and
the theorem `Frontier.P_vs_NP_statement` proves the standard reformulation

  `P ≠ NP ↔ ∃ L, NP L ∧ ¬ P L`,

which is exactly the content of the statement "P ≠ NP" once one knows `P ⊆ NP`
(`Frontier.P_subset_NP`, also proved here).
-/

namespace Frontier

/-- Tape symbols: `none` is the blank symbol, `some b` a bit. -/
abbrev Sym := Option Bool

/-- A language is a set of finite bit strings. -/
abbrev Language := List Bool → Prop

/-- Head movements. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- Apply a head movement to a head position. -/

def NMachine.AcceptsIn (M : NMachine) (x : List Bool) (t : Nat) : Prop :=
  ∃ n, n ≤ t ∧ ∃ c : Cfg M.size,
    M.reaches (M.init x) n c ∧ M.step c = [] ∧ M.accept c.state = true

/-- The class **P**: languages decided by a deterministic Turing machine in polynomial
time. -/
