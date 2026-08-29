/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

universe u v

namespace CS

/-- The complement automaton of a DFA: same states, start state and transition function,
but with the set of accepting states complemented. -/
def complDFA {α : Type u} {σ : Type v} (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := (M.accept)ᶜ

/-- Evaluating the complement automaton is the same as evaluating the original one. -/
theorem complDFA_eval {α : Type u} {σ : Type v} (M : DFA α σ) (x : List α) :
    (complDFA M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement language. -/
theorem accepts_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  show (complDFA M).eval x ∈ (M.accept)ᶜ ↔ x ∈ (M.accepts)ᶜ
  rw [Set.mem_compl_iff, Set.mem_compl_iff, complDFA_eval, DFA.mem_accepts]

/-- **Regular languages are closed under complement.**
If a language `L` is recognized by some DFA with finitely many states, then so is its
complement `Lᶜ`. -/
theorem dfa_complement_regular {T : Type u} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  exact ⟨σ, hσ, complDFA M, by rw [accepts_complDFA, hM]⟩

end CS

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

