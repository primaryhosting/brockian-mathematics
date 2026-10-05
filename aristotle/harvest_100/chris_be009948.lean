/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- The complement automaton of a DFA: same states, same transitions, same start state,
but the accepting states are complemented. -/
def complDFA {T σ : Type} (M : DFA T σ) : DFA T σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

/-- The complement automaton accepts exactly the complement of the language of `M`. -/
theorem accepts_complDFA {T σ : Type} (M : DFA T σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [complDFA, DFA.mem_accepts, DFA.eval, DFA.evalFrom, Set.mem_compl_iff]
  exact Iff.rfl

/-- **Regular languages are closed under complement.**
If `L` is recognized by some finite-state DFA, then so is `Lᶜ`: take the same automaton with
the accepting set complemented. (Mathlib also has this as `Language.IsRegular.compl`.) -/
theorem dfa_complement_regular {T : Type} {L : Language T} (h : L.IsRegular) :
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

