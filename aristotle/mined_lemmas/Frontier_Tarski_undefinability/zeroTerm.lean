/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic and its standard model

We work with the usual first-order language of arithmetic, with constants `0` and `1`,
binary function symbols `+` and `*`, and the binary relation symbol `≤`, interpreted in
the standard model `ℕ`.
-/

/-- Function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- Relation symbols of the language of arithmetic: `≤`. -/
inductive arithRel : ℕ → Type
  | le : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic. -/

def zeroTerm {α : Type} : arith.Term α :=
  Term.func (L := arith) arithFunc.zero (fun i => i.elim0)

/-- The closed term `1`. -/
