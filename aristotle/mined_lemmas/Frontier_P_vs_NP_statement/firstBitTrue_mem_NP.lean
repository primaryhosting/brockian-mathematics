import Mathlib

/-!
# The P vs NP statement

This file gives a self-contained formalization of the statement `P ≠ NP`, together with
all the definitions it depends on:

* single-tape deterministic Turing machines with a *finite* state set (`Frontier.Machine`)
  and their step-counted semantics (`Frontier.Machine.haltCfg`);
* nondeterministic single-tape Turing machines (`Frontier.NMachine`) and their
  time-bounded acceptance semantics (`Frontier.NMachine.AcceptsIn`);
* polynomially bounded time budgets (`Frontier.PolyBound`);
* the classes `Frontier.P` and `Frontier.NP` of languages over the binary alphabet;
* polynomial-time computable functions, polynomial-time many-one reducibility
  `Frontier.PolyReducible` (`≤ₚ`), `Frontier.NPHard` and `Frontier.NPComplete`;
* the statement itself, `Frontier.P_vs_NP_statement : Prop`.

The `P ≠ NP` question is open, so the statement is formalized as a `Prop` (a `def`), not
proved.  What *is* proved here are the sanity results: `P ⊆ NP`, the equivalent
formulation `P ≠ NP ↔ ∃ L ∈ NP, L ∉ P`, and reflexivity of `≤ₚ`.

Finiteness of the state set is essential: with an infinite state set one could smuggle the
answer into the transition function and every language would be decidable in linear time.
The tape alphabet is `Option Bool` (`none` = blank).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-- Words over the binary alphabet. -/
abbrev Word := List Bool

/-- A language is a set of binary words. -/
abbrev Language := Set Word

/-- Tape symbols: `none` is the blank symbol. -/
abbrev Sym := Option Bool

/-- Direction of a head move. -/
inductive Dir
  | left
  | right
  deriving DecidableEq, Repr

/-- A configuration of a machine with `n` states: the current state, the reversed tape
content strictly left of the head, the symbol under the head, and the tape content
strictly right of the head.  Cells not represented in the lists are blank. -/
structure Cfg (n : ℕ) where
  state : Fin n
  left : List Sym
  cur : Sym
  right : List Sym

namespace Cfg

/-- The output of a configuration: the symbols from the head position rightwards, up to
the first blank. -/

theorem firstBitTrue_mem_NP : FirstBitTrue ∈ NP := P_subset_NP firstBitTrue_mem_P

end Frontier

import Mathlib
import RequestProject.Frontier

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

