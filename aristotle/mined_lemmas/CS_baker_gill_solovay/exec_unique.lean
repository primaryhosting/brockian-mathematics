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

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## An oracle machine model

This file develops a small but genuine model of *oracle computation*: a structured
imperative language over string-valued registers, with a cost model in which every
executed instruction costs `1 + (length of the value it writes)`.  Machines are
finite syntactic objects, hence the set of machines is countable (this is what makes
diagonalisation possible), and the cost model is polynomially equivalent to the usual
multitape Turing machine model.
-/

set_option autoImplicit false

namespace CS.BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented by its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A store assigns a string to each register index. -/
abbrev Store := ℕ → Str

/-- Branching conditions. -/
inductive Cond where
  | isNil : ℕ → Cond
  | headTrue : ℕ → Cond
  | eq : ℕ → ℕ → Cond

/-- Evaluation of a branching condition in a store. -/

theorem exec_unique {O : Oracle} {s : Stmt} {st st₁ st₂ : Store} {c₁ c₂ : ℕ}
    {lg₁ lg₂ : List Str} (h1 : Exec O s st st₁ c₁ lg₁) (h2 : Exec O s st st₂ c₂ lg₂) :
    st₁ = st₂ ∧ c₁ = c₂ ∧ lg₁ = lg₂ := by
  obtain ⟨n₂, h2'⟩ := h2
  have := exec_run_eq h1 (n := n₂) (by rw [h2'])
  rw [h2'] at this
  simp at this
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

/-- The execution can be taken with the least halting time. -/
