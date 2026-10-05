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

theorem accepts_iff_at (O : Oracle) (s : Stmt) (x w : Str) (t : ℕ) :
    Accepts O s x w t ↔
      (((step O)^[t] (initCfg s x w)).stk = [] ∧ ((step O)^[t] (initCfg s x w)).cost ≤ t ∧
        ((step O)^[t] (initCfg s x w)).st 0 = [true]) := by
  unfold initCfg
  constructor
  · rintro ⟨st, c, lg, hex, hc, ha⟩
    obtain ⟨n, hn, hne⟩ := exec_min hex
    have h1 : n ≤ ((step O)^[n] (⟨[s], initSt x w, 0, []⟩ : Cfg)).cost := steps_le_cost O _ n hne
    rw [hn] at h1
    simp only [] at h1
    have h2 : (step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)
        = (step O)^[n] (⟨[s], initSt x w, 0, []⟩ : Cfg) :=
      halt_stable O _ (by rw [hn]) (le_trans h1 hc)
    rw [h2, hn]
    exact ⟨rfl, hc, ha⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).st,
      ((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).cost,
      ((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).log, ⟨t, ?_⟩, h2, h3⟩
    generalize hc : (step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg) = d at h1 ⊢
    obtain ⟨stk, st', cst, lg⟩ := d
    simp only [] at h1 ⊢
    rw [h1]

/-! ### Runs with a cost bound -/

/-- `Runs O s st st' b`: the program halts, ending in store `st'`, at cost at most `b`. -/
