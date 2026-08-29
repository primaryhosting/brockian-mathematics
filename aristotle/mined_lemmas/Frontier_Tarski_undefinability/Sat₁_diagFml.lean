import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Syntax of the language of arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, ·}`, with variables indexed
by natural numbers. -/
inductive Trm : Type
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

/-- Formulas of the language of arithmetic: atomic equations, negation,
conjunction and universal quantification over a variable. -/
inductive Fml : Type
  | eq : Trm → Trm → Fml
  | not : Fml → Fml
  | and : Fml → Fml → Fml
  | all : ℕ → Fml → Fml
  deriving DecidableEq

/-- Implication, as an abbreviation. -/

theorem Sat₁_diagFml (T : Fml) (a : ℕ) : Sat₁ (diagFml T) a ↔ ¬ Sat₂ T a a := by
  have key : (∀ m : ℕ, (Fml.imp (Fml.eq (Trm.var 1) (Trm.var 0)) T).Sat
      (Function.update (asg₁ a) 1 m)) ↔ Sat₂ T a a := by
    constructor
    · intro h
      have h' := h a
      simp only [Fml.Sat_imp, Fml.Sat_eq, Trm.eval, update_asg₁_apply_zero,
        update_asg₁_apply_one] at h'
      have h'' := h' rfl
      rwa [update_asg₁_eq_asg₂] at h''
    · intro h m
      simp only [Fml.Sat_imp, Fml.Sat_eq, Trm.eval, update_asg₁_apply_zero,
        update_asg₁_apply_one]
      rintro rfl
      rwa [update_asg₁_eq_asg₂]
  simp only [Sat₁, diagFml, Fml.Sat_not, Fml.Sat_all]
  rw [key]

/-! ## Tarski's undefinability theorem -/

/-- **Tarski's undefinability of truth.**  Arithmetical truth is not arithmetically
definable: there is no formula `T` of the language of arithmetic and no Gödel
numbering `code : Fml → ℕ` such that, for every formula `F` and every natural
number `a`, the formula `T` is true in `ℕ` at `(⌜F⌝, a)` if and only if `F` is
true in `ℕ` at `a`.

No effectiveness (not even injectivity) is assumed of the numbering `code`, so
the statement is stronger than the usual formulation for an effective Gödel
numbering. -/
