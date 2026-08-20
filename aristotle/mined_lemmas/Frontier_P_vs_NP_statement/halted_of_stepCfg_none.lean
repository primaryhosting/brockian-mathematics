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

theorem halted_of_stepCfg_none {c : Cfg M.size} (h : M.stepCfg c = none) :
    M.toNMachine.Halted c := by
  simp only [NMachine.Halted, toNMachine, Option.toList_eq_nil_iff]
  rcases hstep : M.step c.state c.cur with _ | tr
  · rfl
  · rw [stepCfg, hstep] at h; simp at h

