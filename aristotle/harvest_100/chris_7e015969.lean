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

namespace CS

universe u v

/-- The *complement automaton* of a DFA `M`: the same states, transition function and start
state, but with the set of accepting states replaced by its complement. -/
def complDFA {α : Type u} {σ : Type v} (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := (M.accept)ᶜ

/-- The complement automaton accepts exactly the words that `M` rejects. -/
theorem accepts_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [DFA.mem_accepts, complDFA, Set.mem_compl_iff, DFA.eval, DFA.evalFrom]
  rfl

/-- **Regular languages are closed under complement.**
If a language `L` over an alphabet `T` is regular (i.e. recognized by some DFA with finitely
many states), then its complement `Lᶜ` is regular as well. -/
theorem dfa_complement_regular {T : Type u} {L : Language T} (h : L.IsRegular) :
    (Lᶜ : Language T).IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  exact ⟨σ, hσ, complDFA M, by rw [accepts_complDFA, hM]⟩

end CS

