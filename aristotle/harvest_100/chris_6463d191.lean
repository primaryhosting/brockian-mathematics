import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u v

namespace CS

open Language

/-- The complement automaton: same states, transitions and start state, with the
accepting set replaced by its complement. -/
def complDFA {T : Type u} {σ : Type v} (M : DFA T σ) : DFA T σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

/-- The complement automaton accepts exactly the complement language. -/
theorem accepts_complDFA {T : Type u} {σ : Type v} (M : DFA T σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom, complDFA, Set.compl_def,
    Set.mem_setOf_eq]
  rfl

/-- Regular languages are closed under complement. -/
theorem dfa_complement_regular {T : Type u} {L : Language T} (h : L.IsRegular) :
    (Lᶜ : Language T).IsRegular := by
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

