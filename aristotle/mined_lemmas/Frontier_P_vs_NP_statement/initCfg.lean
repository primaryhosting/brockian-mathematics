/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
/-!
## Overview

This file is a self-contained formalisation (it needs no imports beyond the Lean core
prelude, so that the module header above can literally begin the file) of:

* single-tape Turing machines over the binary alphabet, deterministic (`Frontier.DTM`) and
  nondeterministic (`Frontier.NTM`), with a *finite* state set `Fin (states + 1)`;
* their step semantics on a two-way infinite tape `Int → Sym`;
* time-bounded decision of a language, and the complexity classes `Frontier.P` and
  `Frontier.NP`;
* polynomial-time computable functions, Karp (polynomial-time many-one) reducibility
  `Frontier.PolyReducible`, NP-hardness and NP-completeness.

The target declaration `Frontier.P_vs_NP_statement` states the precise content of the
assertion `P ≠ NP`: the classes differ exactly when some language is decided by a
polynomial-time nondeterministic Turing machine but by no polynomial-time deterministic one.
The theorem is the conjunction of the (proved) inclusion `P ⊆ NP` with pure logic; the
assertion `P ≠ NP` itself is of course open, and is *not* proved here.
-/

namespace Frontier

/-! ## Words, languages, tapes -/

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A word is a finite binary string. -/
abbrev Word : Type := List Bool

/-- A language is a set of binary words. -/
abbrev Language : Type := Word → Prop

/-- The initial tape holding the input word `x`: the `i`-th cell (for `i ≥ 0`) holds the
`i`-th bit of `x`, and all other cells are blank. -/

def initCfg (n : Nat) (x : Word) : Cfg (n + 1) := ⟨0, initTape x, 0⟩

/-! ## Deterministic machines and the class `P` -/

/-- A deterministic single-tape Turing machine over the binary alphabet. Its state set is
`Fin (states + 1)`, with `0` the initial state; on state `q` reading symbol `a` it either
halts (`M q a = none`) or moves to a new state performing an instruction. -/
structure DTM : Type where
  /-- The machine has `states + 1` internal states. -/
  states : Nat
  /-- The transition function; `none` means "halt". -/
  M : Fin (states + 1) → Sym → Option (Fin (states + 1) × Stmt)
  /-- The accepting states. -/
  accept : Fin (states + 1) → Prop

/-- One step of a deterministic machine; `none` means the machine has halted. -/
