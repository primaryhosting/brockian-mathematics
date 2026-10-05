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

theorem length_invariant (O : Oracle) (c : Cfg) (m : ℕ)
    (h0 : ∀ i, (c.st i).length ≤ m + c.cost) (n : ℕ) :
    ∀ i, (((step O)^[n] c).st i).length ≤ m + ((step O)^[n] c).cost := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    revert ih
    generalize (step O)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro ih
    simp only [] at ih ⊢
    cases stk with
    | nil => simpa using ih
    | cons a r =>
      cases a with
      | skip => intro i; simpa using le_trans (ih i) (by omega)
      | seq a b => intro i; simpa using le_trans (ih i) (by omega)
      | ifte cd a b => intro i; simpa using le_trans (ih i) (by omega)
      | wh cd a =>
        intro i
        by_cases hc : cd.ev st <;> simp [hc] <;> exact le_trans (ih i) (by omega)
      | lit k v =>
        intro i; simp only [step_lit]
        exact upd_len_bound ih k v (by omega) (by omega) i
      | cat k j l =>
        intro i; simp only [step_cat]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | rep k j l =>
        intro i; simp only [step_rep]
        exact upd_len_bound ih k _ (by simp; omega) (by omega) i
      | tl k j =>
        intro i; simp only [step_tl]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | cns k b j =>
        intro i; simp only [step_cns]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | qry k j =>
        intro i; simp only [step_qry]
        refine upd_len_bound ih k _ ?_ (by omega) i
        have : ((if O (st j) then [true] else []) : Str).length ≤ 1 := by
          split <;> simp
        omega

/-- Every queried string is short: at most the initial maximal length plus the cost. -/
