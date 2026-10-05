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

theorem exec_wh_true {O : Oracle} {cd : Cond} {a : Stmt} {st st₁ st₂ : Store} {c₁ c₂ : ℕ}
    {lg₁ lg₂ : List Str} (h : cd.ev st = true) (h1 : Exec O a st st₁ c₁ lg₁)
    (h2 : Exec O (.wh cd a) st₁ st₂ c₂ lg₂) :
    Exec O (.wh cd a) st st₂ (c₁ + c₂ + 1) (lg₂ ++ lg₁) := by
  obtain ⟨n₁, hn₁, hne₁⟩ := exec_min h1
  obtain ⟨n₂, hn₂, hne₂⟩ := exec_min h2
  refine ⟨n₂ + (n₁ + 1), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have hstep : (step O)^[1] (⟨[Stmt.wh cd a], st, 0, []⟩ : Cfg)
      = ⟨[a, Stmt.wh cd a], st, 1, []⟩ := by simp [h]
  rw [hstep, show (⟨[a, Stmt.wh cd a], st, 1, []⟩ : Cfg)
      = shift [Stmt.wh cd a] 1 [] ⟨[a], st, 0, []⟩ from by simp [shift],
    iterate_shift O _ n₁ hne₁ _ 1 [], hn₁]
  simp only [shift, List.nil_append, List.append_nil]
  rw [show (⟨[Stmt.wh cd a], st₁, c₁ + 1, lg₁⟩ : Cfg)
      = shift [] (c₁ + 1) lg₁ ⟨[Stmt.wh cd a], st₁, 0, []⟩ from by simp [shift],
    iterate_shift O _ n₂ hne₂ [] (c₁ + 1) lg₁, hn₂]
  simp only [shift, List.append_nil, Cfg.mk.injEq]
  exact ⟨trivial, trivial, by omega, trivial⟩

end CS.BGS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGS.Exec

/-!
## The relativised classes `P^O` and `N P^O`
-/

set_option autoImplicit false

namespace CS.BGS

open Filter Asymptotics

/-- The polynomial time bounds we quantify over: `tb k n = (n+2)^k`.
Every polynomial is dominated by one of these, and each of these is a polynomial. -/
