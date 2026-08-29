/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace CS

open Language

/-- The complement automaton: same states, same transitions, same start state, but the set of
accepting states is complemented. -/
def complDFA {α : Type u} {σ : Type v} (M : DFA α σ) : DFA α σ :=
  { step := M.step, start := M.start, accept := M.acceptᶜ }

@[simp]
theorem eval_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) (x : List α) :
    (complDFA M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement of the language of `M`. -/
theorem accepts_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [DFA.mem_accepts, eval_complDFA]
  rfl

/-- **Regular languages are closed under complement.**
If `L` is regular, so is its complement `Lᶜ`. -/
theorem dfa_complement_regular {α : Type u} {L : Language α} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  exact ⟨σ, hσ, complDFA M, by rw [accepts_complDFA, hM]⟩

/-- The complement version is an equivalence: `Lᶜ` is regular iff `L` is. -/
theorem dfa_complement_regular_iff {α : Type u} {L : Language α} :
    Lᶜ.IsRegular ↔ L.IsRegular := by
  refine ⟨fun h => ?_, dfa_complement_regular⟩
  simpa using dfa_complement_regular h

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

