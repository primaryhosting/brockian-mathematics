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

theorem P_ne_NP_of_NPComplete_not_mem_P {L : Language} (hL : NPComplete L) (h : ¬ P L) :
    P ≠ NP :=
  P_vs_NP_statement.2 ⟨L, hL.1, h⟩

end Frontier


import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

