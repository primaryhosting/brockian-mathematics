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

theorem query_length_bound (O : Oracle) (c : Cfg) (m : ℕ)
    (h0 : ∀ i, (c.st i).length ≤ m + c.cost) (hlog : ∀ s ∈ c.log, s.length ≤ m + c.cost)
    (n : ℕ) : ∀ s ∈ ((step O)^[n] c).log, s.length ≤ m + ((step O)^[n] c).cost := by
  induction n with
  | zero => simpa using hlog
  | succ n ih =>
    have hst : ∀ i, (((step O)^[n] c).st i).length ≤ m + ((step O)^[n] c).cost :=
      length_invariant O c m h0 n
    rw [Function.iterate_succ_apply']
    revert ih hst
    generalize (step O)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro ih hst
    simp only [] at ih hst ⊢
    cases stk with
    | nil => simpa using ih
    | cons a r =>
      cases a with
      | skip => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | seq a b => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | ifte cd a b => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | wh cd a =>
        intro s hs
        by_cases hc : cd.ev st <;> simp [hc] at hs ⊢ <;> exact le_trans (ih s hs) (by omega)
      | lit k v => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | cat k j l => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | rep k j l => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | tl k j => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | cns k b j => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | qry k j =>
        intro s hs
        simp only [step_qry, List.mem_cons] at hs ⊢
        rcases hs with h | h
        · subst h; exact le_trans (hst j) (by omega)
        · exact le_trans (ih s h) (by omega)

/-! ### The number of queries is at most the number of steps -/

