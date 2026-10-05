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

theorem locality (O₁ O₂ : Oracle) (c : Cfg) (n : ℕ)
    (h : ∀ s ∈ ((step O₁)^[n] c).log, O₁ s = O₂ s) :
    (step O₁)^[n] c = (step O₂)^[n] c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsuf : ((step O₁)^[n] c).log <:+ ((step O₁)^[n+1] c).log :=
      log_suffix_mono O₁ c (Nat.le_succ n)
    have ih' : (step O₁)^[n] c = (step O₂)^[n] c :=
      ih (fun s hs => h s (hsuf.mem hs))
    have h' : ∀ s ∈ (step O₁ ((step O₁)^[n] c)).log, O₁ s = O₂ s := by
      intro s hs
      exact h s (by rw [Function.iterate_succ_apply']; exact hs)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih']
    revert h'
    generalize (step O₁)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro h'
    cases stk with
    | nil => simp
    | cons a r =>
      cases a with
      | qry i j =>
        have hq : O₁ (st j) = O₂ (st j) := by
          apply h'
          simp
        simp [hq]
      | skip => simp
      | seq a b => simp
      | ifte cd a b => simp
      | wh cd a => simp
      | lit i v => simp
      | cat i j k => simp
      | rep i j k => simp
      | tl i j => simp
      | cns i b j => simp

/-! ### Length invariant -/

