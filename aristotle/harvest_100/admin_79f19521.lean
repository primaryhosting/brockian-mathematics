/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file structure: in Lean 4 an `import` command must be the very first command of a
file, and a `/-! ... -/` module documentation block already counts as a command.  Since the
file is required to begin with the header block above, this module is written to be fully
self-contained: it develops deterministic finite automata, regular languages and the
complement construction from first principles, using nothing beyond Lean's core `Init`
library.  A companion module, `RequestProject.DfaComplementRegularMathlib`, states and proves
the same closure result for Mathlib's `Language.IsRegular`.
-/

set_option autoImplicit false

universe u v

namespace CS

/-- A language over the alphabet `α` is a predicate on words (finite lists of letters). -/
def Lang (α : Type u) : Type u := List α → Prop

/-- The complement of a language. -/
def Lang.compl {α : Type u} (L : Lang α) : Lang α := fun x => ¬ L x

/-- A deterministic finite automaton: a transition function, a start state and a set of
accepting states.  Finiteness of the state type is imposed separately, in `Language.IsRegular`. -/
structure DFAut (α : Type u) (σ : Type v) where
  /-- The transition function. -/
  step : σ → α → σ
  /-- The initial state. -/
  start : σ
  /-- The set of accepting states. -/
  accept : σ → Prop

namespace DFAut

variable {α : Type u} {σ : Type v}

/-- Run the automaton on a word, starting from the given state. -/
def evalFrom (M : DFAut α σ) (s : σ) (x : List α) : σ := List.foldl M.step s x

/-- Run the automaton on a word, starting from its initial state. -/
def eval (M : DFAut α σ) (x : List α) : σ := M.evalFrom M.start x

/-- The language accepted by an automaton. -/
def accepts (M : DFAut α σ) : Lang α := fun x => M.accept (M.eval x)

end DFAut

/-- A type is finite when some list enumerates all of its elements. -/
def IsFiniteType (σ : Type) : Prop := ∃ l : List σ, ∀ s : σ, s ∈ l

/-- A language is regular when it is the language of some automaton with finitely many
states. -/
def Lang.IsRegular {α : Type u} (L : Lang α) : Prop :=
  ∃ σ : Type, IsFiniteType σ ∧ ∃ M : DFAut α σ, ∀ x, M.accepts x ↔ L x

/-- The complement automaton: the same transitions and initial state, with the accepting and
non-accepting states interchanged. -/
def complDFAut {α : Type u} {σ : Type v} (M : DFAut α σ) : DFAut α σ where
  step := M.step
  start := M.start
  accept := fun s => ¬ M.accept s

@[simp]
theorem complDFAut_eval {α : Type u} {σ : Type v} (M : DFAut α σ) (x : List α) :
    (complDFAut M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement of the original language. -/
theorem accepts_complDFAut {α : Type u} {σ : Type v} (M : DFAut α σ) (x : List α) :
    (complDFAut M).accepts x ↔ ¬ M.accepts x := Iff.rfl

/-- **Regular languages are closed under complement.**

Given a DFA `M` with finitely many states recognizing `L`, the automaton `complDFAut M`,
which has the same states, transitions and start state but the complementary set of accepting
states, has finitely many states and recognizes the complement of `L`. -/
theorem dfa_complement_regular {α : Type u} {L : Lang α} (h : L.IsRegular) :
    L.compl.IsRegular := by
  obtain ⟨σ, hfin, M, hM⟩ := h
  refine ⟨σ, hfin, complDFAut M, fun x => ?_⟩
  simpa [Lang.compl, accepts_complDFAut] using not_congr (hM x)

end CS

/-- info: 'CS.dfa_complement_regular' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CS.dfa_complement_regular

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

import Mathlib

/-!
# Dfa Complement Regular (Mathlib formulation)

Companion module to `RequestProject.DfaComplementRegular`: the same closure property, stated
for Mathlib's `Language.IsRegular`, and proved by the explicit complement construction on
deterministic finite automata (rather than by invoking Mathlib's `Language.IsRegular.compl`).
-/

set_option autoImplicit false

universe u v

namespace CS

/-- The complement automaton of a DFA: same transitions and start state, complemented set of
accepting states. -/
def complDFA {α : Type u} {σ : Type v} (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

@[simp]
theorem complDFA_evalFrom {α : Type u} {σ : Type v} (M : DFA α σ) (s : σ) (x : List α) :
    (complDFA M).evalFrom s x = M.evalFrom s x := rfl

/-- The complement automaton accepts exactly the complement of the original language. -/
theorem accepts_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [DFA.accepts, DFA.acceptsFrom, complDFA, Set.mem_setOf_eq, Set.compl_def]
  exact Iff.rfl

/-- Regular languages are closed under complement (Mathlib's `Language.IsRegular`). -/
theorem language_isRegular_compl {T : Type u} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  exact ⟨σ, hσ, complDFA M, by rw [accepts_complDFA, hM]⟩

end CS

/-- info: 'CS.language_isRegular_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CS.language_isRegular_compl

