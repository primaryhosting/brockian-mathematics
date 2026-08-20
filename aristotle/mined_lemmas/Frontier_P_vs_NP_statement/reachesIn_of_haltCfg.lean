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

theorem reachesIn_of_haltCfg :
    ∀ (t : ℕ) (c c' : Cfg M.size), M.haltCfg t c = some c' →
      ∃ k ≤ t, M.toNMachine.ReachesIn k c c' ∧ M.toNMachine.Halted c' := by
  intro t
  induction t with
  | zero =>
      intro c c' h
      simp only [haltCfg] at h
      rcases hs : M.stepCfg c with _ | d
      · rw [hs] at h
        simp only [Option.isNone_none, if_true, Option.some.injEq] at h
        exact ⟨0, le_rfl, h, h ▸ M.halted_of_stepCfg_none hs⟩
      · rw [hs] at h; simp at h
  | succ t ih =>
      intro c c' h
      simp only [haltCfg] at h
      rcases hs : M.stepCfg c with _ | d
      · rw [hs] at h
        simp only [Option.some.injEq] at h
        exact ⟨0, Nat.zero_le _, h, h ▸ M.halted_of_stepCfg_none hs⟩
      · rw [hs] at h
        obtain ⟨k, hk, hreach, hhalt⟩ := ih d c' h
        exact ⟨k + 1, Nat.succ_le_succ hk, ⟨d, M.stepRel_of_stepCfg hs, hreach⟩, hhalt⟩

