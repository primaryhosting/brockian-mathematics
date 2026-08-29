import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands in a
file, so the header comment above is placed immediately after the single `import Mathlib`
line; its text is otherwise verbatim.
-/

open Computability

namespace CS

variable {α : Type*} {σ : Type*}

/-- The complement automaton of a DFA: same transition function and start state,
but the accepting states are complemented. -/
def DFA.compl (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

@[simp]
theorem DFA.compl_eval (M : DFA α σ) (x : List α) : (DFA.compl M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement language. -/
theorem DFA.accepts_compl (M : DFA α σ) : (DFA.compl M).accepts = M.acceptsᶜ := rfl

/-- **Regular languages are closed under complement.**
If `L` is regular (accepted by some DFA with finitely many states), then so is `Lᶜ`.
The proof is by the explicit complement-automaton construction `CS.DFA.compl`.
(Mathlib also provides this as `Language.IsRegular.compl`.) -/
theorem dfa_complement_regular {T : Type*} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, _, M, hM⟩ := h
  exact ⟨σ, ‹Fintype σ›, DFA.compl M, by rw [DFA.accepts_compl, hM]⟩

/-- The converse direction: `Lᶜ` regular implies `L` regular, hence regularity of a language
and of its complement are equivalent. -/
theorem dfa_complement_regular_iff {T : Type*} {L : Language T} :
    Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨fun h => by simpa using dfa_complement_regular h, dfa_complement_regular⟩

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

