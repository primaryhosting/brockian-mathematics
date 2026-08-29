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

def Sat₁ (F : Fml) (a : ℕ) : Prop := F.Sat (asg₁ a)

/-- `Sat₂ F a b` says that `F` is true in `ℕ` when `x₀ ↦ a` and `x₁ ↦ b`
(and all other variables get the value `0`). -/
